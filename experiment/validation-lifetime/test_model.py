"""Run: python3 -m unittest discover -s experiment/validation-lifetime -v."""
from itertools import product
import unittest

from model import (
    Accepted, Blocked, Invalid, Misuse, NUMBER, STRING, BOTTOM, Observation,
    Owner, Proposal, Query, Ty, atom, join, normalize, record, tup,
)


def sub(a: Ty, b: Ty) -> Query:
    return Query("sub", a, b)


class LifetimeTests(unittest.TestCase):
    def test_probe_cannot_authorize_acceptance(self):
        owner = Owner()
        proposal = owner.probe(sub(NUMBER, NUMBER))
        with self.assertRaises(Misuse):
            owner.use(proposal)
        owner.use(owner.replay(proposal), sub(NUMBER, NUMBER))

    def test_clone_only_solution_is_not_parent_solution(self):
        owner = Owner()
        v = owner.fresh()
        before = owner.snapshot
        proposal = owner.probe(sub(NUMBER, v), lambda child: child.bind(v, NUMBER))
        self.assertTrue(proposal.preview)
        self.assertEqual(owner.snapshot, before)
        with self.assertRaises(Blocked):
            owner.replay(proposal)
        with self.assertRaises(Blocked):
            owner.finish()  # Catching the error does not erase the obligation.

    def test_replay_checks_current_parent_not_preview(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        proposal = owner.probe(sub(v, NUMBER))
        owner.grow(v, STRING)
        with self.assertRaises(Invalid):
            owner.replay(proposal)

    def test_nonmutating_probe_is_not_permanently_valid(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        proposal = owner.probe(sub(v, NUMBER))
        receipt = owner.replay(proposal)
        owner.grow(v, STRING)
        with self.assertRaises(Invalid):
            owner.use(receipt)

    def test_seal_in_clone_does_not_seal_parent(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        proposal = owner.probe(sub(v, NUMBER), lambda child: child.seal(v))
        owner.replay(proposal)
        self.assertTrue(owner.grow(v, STRING))
        with self.assertRaises(Invalid):
            owner.finish()

    def test_closed_outer_binding_retains_transitive_dependency(self):
        owner = Owner()
        outer, inner = owner.fresh(), owner.fresh()
        owner.bind(inner, NUMBER)
        owner.bind(outer, inner, closed=True)
        receipt = owner.require(sub(outer, NUMBER))
        owner.grow(inner, STRING)
        with self.assertRaises(Invalid):
            owner.use(receipt)

    def test_frozen_answer_keeps_original_normalization_premise(self):
        owner = Owner()
        element = owner.fresh()
        owner.bind(element, NUMBER)
        operation = Ty("element", (tup(element),))
        result = owner.observe(operation)
        owner.require(sub(result.value, NUMBER))
        owner.grow(element, STRING)
        self.assertTrue(sub(result.value, NUMBER).holds(owner.snapshot))
        with self.assertRaises(Invalid):
            owner.consume(result)
        with self.assertRaises(Invalid):
            owner.finish()  # Frozen downstream operands alone would incorrectly pass.

    def test_fresh_recomputation_after_growth(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        owner.grow(v, STRING)
        result = owner.observe(Ty("element", (tup(v),)))
        self.assertEqual(owner.consume(result), join(NUMBER, STRING))
        owner.publish(owner.finish())

    def test_shape_observations_are_gated(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, tup(NUMBER))
        result = owner.observe(Ty("arity", (shape,)))
        self.assertEqual(owner.consume(result), atom("arity:1"))
        owner.grow(shape, tup())
        with self.assertRaises(Blocked):
            owner.finish()  # A union of tuple shapes is deliberately unsupported here.

    def test_key_projection_does_not_forget_nested_provenance(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, record(value=NUMBER))
        result = owner.observe(Ty("keys", (shape,)))
        self.assertEqual(result.value, atom("key:value"))
        owner.grow(shape, record(other=STRING))
        with self.assertRaises(Blocked):
            owner.consume(result)

    def test_unbound_is_not_bottom(self):
        owner = Owner()
        v = owner.fresh()
        with self.assertRaises(Blocked):
            owner.require(sub(v, NUMBER))
        owner.bind(v, NUMBER)
        owner.publish(owner.finish())
        owner.require(sub(BOTTOM, NUMBER))  # Explicit bottom is a different case.

    def test_noop_growth_does_not_prove_compatibility(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER, closed=True)
        self.assertFalse(owner.grow(v, STRING))
        with self.assertRaises(Invalid):
            owner.require(sub(STRING, v))
        with self.assertRaises(Invalid):
            owner.finish()

    def test_unrelated_growth_replays_without_false_rejection(self):
        owner = Owner()
        x, y = owner.fresh(), owner.fresh()
        owner.bind(x, NUMBER)
        owner.bind(y, NUMBER)
        receipt = owner.require(sub(x, NUMBER))
        before = owner.evaluations
        owner.grow(y, STRING)
        refreshed = owner.use(receipt)
        self.assertEqual(owner.evaluations, before + 1)
        self.assertNotEqual(refreshed.stamp, receipt.stamp)

    def test_same_snapshot_uses_checked_cache(self):
        owner = Owner()
        receipt = owner.require(sub(NUMBER, NUMBER))
        before = owner.evaluations
        self.assertEqual(owner.use(receipt), receipt)
        owner.publish(owner.finish())
        self.assertEqual(owner.evaluations, before)

    def test_validation_is_read_only(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        before = owner.snapshot
        owner.require(sub(v, NUMBER))
        owner.observe(tup(v))
        owner.publish(owner.finish())
        self.assertEqual(owner.snapshot, before)
        self.assertFalse(dict(before.bindings)[v.label].closed)

    def test_rollback_does_not_resurrect_old_acceptance(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        owner.require(sub(v, NUMBER))
        checkpoint = owner.save()
        old = owner.finish()
        owner.grow(v, STRING)
        owner.restore(checkpoint)
        self.assertNotEqual(old.stamp, owner.snapshot.stamp)
        with self.assertRaises(Misuse):
            owner.publish(old)
        owner.publish(owner.finish())

    def test_rollback_regrowth_same_numeric_version_is_not_same_state(self):
        owner = Owner()
        v = owner.fresh()
        checkpoint = owner.save()
        owner.bind(v, NUMBER)
        old_version = owner.legacy_version
        receipt = owner.require(sub(v, NUMBER))
        owner.restore(checkpoint)
        owner.bind(v, STRING)
        self.assertEqual(old_version, owner.legacy_version)
        self.assertNotEqual(receipt.stamp, owner.snapshot.stamp)
        with self.assertRaises(Misuse):
            owner.use(receipt)
        with self.assertRaises(Invalid):
            owner.require(sub(v, NUMBER))

    def test_rollback_removes_failed_alternative_obligations(self):
        owner = Owner()
        checkpoint = owner.save()
        with self.assertRaises(Invalid):
            owner.require(sub(STRING, NUMBER))
        with self.assertRaises(Invalid):
            owner.finish()
        owner.restore(checkpoint)
        owner.publish(owner.finish())

    def test_late_dependency_after_rollback_is_still_followed(self):
        owner = Owner()
        outer, inner = owner.fresh(), owner.fresh()
        owner.bind(inner, NUMBER)
        owner.bind(outer, inner, closed=True)
        receipt = owner.require(sub(outer, NUMBER))
        checkpoint = owner.save()
        owner.grow(inner, STRING)
        with self.assertRaises(Invalid):
            owner.use(receipt)
        owner.restore(checkpoint)
        owner.use(receipt)
        owner.grow(inner, STRING)
        with self.assertRaises(Invalid):
            owner.finish()

    def test_evidence_cannot_cross_owner_or_scope(self):
        owner, other = Owner(), Owner()
        receipt = owner.require(sub(NUMBER, NUMBER))
        with self.assertRaises(Misuse):
            other.use(receipt)
        with self.assertRaises(Misuse):
            other.replay(owner.probe(sub(NUMBER, NUMBER)))
        with self.assertRaises(Misuse):
            other.publish(owner.finish())

    def test_clone_and_rollback_allocations_never_reuse_identity(self):
        owner = Owner()
        child = owner._fork()
        child_var = child.fresh()
        live_var = owner.fresh()
        self.assertNotEqual(child_var, live_var)
        with self.assertRaises(Blocked):
            normalize(child_var, owner.snapshot)
        checkpoint = owner.save()
        discarded = owner.fresh()
        owner.restore(checkpoint)
        self.assertNotEqual(discarded, owner.fresh())

    def test_mode_changes_invalidate_receipts_and_are_inherited_by_clones(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        receipt = owner.require(sub(v, NUMBER))
        owner.set_mode("frozen")
        child = owner._fork()
        self.assertEqual(child.snapshot.mode, "frozen")
        self.assertFalse(child.grow(v, STRING))
        frozen_receipt = owner.use(receipt)
        self.assertNotEqual(receipt.stamp, frozen_receipt.stamp)
        owner.set_mode("normal")
        owner.grow(v, STRING)
        with self.assertRaises(Invalid):
            owner.use(frozen_receipt)

    def test_publication_covers_obligation_set_not_just_substitution(self):
        owner = Owner()
        owner.require(sub(NUMBER, NUMBER))
        accepted = owner.finish()
        with self.assertRaises(Invalid):
            owner.require(sub(STRING, NUMBER))
        self.assertEqual(accepted.stamp, owner.snapshot.stamp)
        with self.assertRaises(Misuse):
            owner.publish(accepted)

    def test_wrong_judgment_and_wrong_materialization_are_rejected(self):
        owner = Owner()
        receipt = owner.require(sub(NUMBER, NUMBER))
        with self.assertRaises(Misuse):
            owner.use(receipt, sub(STRING, NUMBER))
        observed = owner.observe(NUMBER)
        with self.assertRaises(Misuse):
            owner.consume(Observation(STRING, observed.receipt))
        with self.assertRaises(Misuse):
            owner.consume(Observation(NUMBER, receipt))

    def test_recursive_candidate_graph_is_blocked_not_assumed_valid(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, tup(v), closed=True)
        with self.assertRaises(Blocked):
            owner.require(sub(v, NUMBER))
        with self.assertRaises(Blocked):
            owner.finish()

    def test_final_publication_retires_inference_owner(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        owner.require(sub(v, NUMBER))
        saved = owner.save()
        final = owner.close()
        owner.publish(final)
        for action in (
            lambda: owner.grow(v, STRING), lambda: owner.fresh(),
            lambda: owner.restore(saved), lambda: owner.require(sub(STRING, NUMBER)),
        ):
            with self.assertRaises(Misuse):
                action()
        owner.publish(final)

    def test_bounded_state_space(self):
        # 2 initial types * 7 nonempty targets * 8^3 action traces = 7168 cases.
        # This enumerates only this finite model, not SKJS executions.
        atoms = (NUMBER, STRING, atom("boolean"))
        targets = [join(*(a for j, a in enumerate(atoms) if bits & (1 << j))) for bits in range(1, 8)]
        actions = ("number", "string", "boolean", "save", "restore", "freeze", "thaw", "seal")
        cases = 0
        for initial, target, trace in product(atoms[:2], targets, product(actions, repeat=3)):
            owner = Owner()
            outer, inner = owner.fresh(), owner.fresh()
            owner.bind(inner, initial)
            owner.bind(outer, inner, closed=True)
            query = sub(outer, target)
            # Include originally failing obligations; later growth may legitimately settle them.
            try:
                receipt = owner.require(query)
            except Invalid:
                receipt = None
            checkpoint = owner.save()
            expected_values = {initial.label}
            saved_values = set(expected_values)
            is_closed = False
            saved_closed = False
            frozen = False
            saved_frozen = False
            for action in trace:
                if action == "save":
                    checkpoint = owner.save()
                    saved_values, saved_closed, saved_frozen = set(expected_values), is_closed, frozen
                elif action == "restore":
                    owner.restore(checkpoint)
                    expected_values, is_closed, frozen = set(saved_values), saved_closed, saved_frozen
                elif action in ("freeze", "thaw"):
                    frozen = action == "freeze"
                    owner.set_mode("frozen" if frozen else "normal")
                elif action == "seal":
                    owner.seal(inner)
                    is_closed = is_closed or not frozen
                else:
                    owner.grow(inner, atom(action))
                    if not is_closed and not frozen:
                        expected_values.add(action)
                target_values = {a.label for a in target.args} if target.op == "union" else {target.label}
                expected = expected_values <= target_values  # Independent finite-set oracle.
                try:
                    accepted = owner.finish()
                    owner.publish(accepted)
                    actual = True
                except Invalid:
                    actual = False
                self.assertEqual(actual, expected, (initial, target, trace, action))
                if receipt is not None:
                    try:
                        owner.use(receipt)
                        reused = True
                    except Invalid:
                        reused = False
                    self.assertEqual(reused, expected)
            cases += 1
        self.assertEqual(cases, 7168)


if __name__ == "__main__":
    unittest.main()
