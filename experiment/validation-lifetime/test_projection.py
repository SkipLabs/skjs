"""Tests of the complete reference path, not executions of the SKJS binary."""
from dataclasses import replace
from itertools import product
import unittest

from model import (
    BOTTOM, NUMBER, STRING, Blocked, Invalid, Misuse, Owner, Ty, atom, join, tup,
)
from projection import (
    Catalog, Definition, Derived, ProjectionPipeline, ShapeQuery,
    alias, array, element, parameter,
)


ELEMENTS = "stdlib/types.ts#ElementOf/0"
VECTOR = "stdlib/types.ts#Vector/0"
IDENTITY = "stdlib/types.ts#Id/0"
CATALOG = Catalog((
    Definition(ELEMENTS, 1, Ty("element", (parameter(0),))),
    Definition(VECTOR, 1, array(parameter(0))),
    Definition(IDENTITY, 1, parameter(0)),
))


def expect(pipe, value, target):
    return pipe.require_subtype(value, pipe.source(target))


def indexed(pipe, operand):
    return pipe.instantiate(pipe.source(alias(ELEMENTS, operand)))


class ProjectionTests(unittest.TestCase):
    def test_source_alias_projection_consumer_publication_path(self):
        owner = Owner()
        element_var = owner.fresh()
        owner.bind(element_var, NUMBER)
        pipe = ProjectionPipeline(owner, CATALOG)
        result = indexed(pipe, alias(VECTOR, element_var))
        expect(pipe, result, NUMBER)
        pipe.close()

    def test_symbolic_projection_does_not_solve_an_unbound_element(self):
        owner = Owner()
        v = owner.fresh()
        pipe = ProjectionPipeline(owner, CATALOG)
        before = owner.snapshot
        result = indexed(pipe, array(v))
        self.assertEqual(pipe.display(result), repr(v))
        self.assertEqual(owner.snapshot, before)
        owner.bind(v, NUMBER)
        expect(pipe, result, NUMBER)
        self.assertFalse(dict(owner.snapshot.bindings)[v.label].closed)
        pipe.close()

    def test_symbolic_result_allows_compatible_later_growth(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        pipe = ProjectionPipeline(owner, CATALOG)
        result = indexed(pipe, array(v))
        expect(pipe, result, join(NUMBER, STRING))
        owner.grow(v, STRING)
        self.assertEqual(pipe.display(result), repr(v))
        pipe.close()

    def test_symbolic_result_still_revalidates_downstream_subtype(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        pipe = ProjectionPipeline(owner, CATALOG)
        result = indexed(pipe, array(v))
        expect(pipe, result, NUMBER)
        owner.grow(v, STRING)
        # Projection equality remains true, but the numeric obligation doesn't.
        self.assertEqual(pipe.display(result), repr(v))
        with self.assertRaises(Invalid):
            pipe.close()

    def test_frozen_answer_keeps_transitive_projection_provenance(self):
        owner = Owner()
        outer, inner = owner.fresh(), owner.fresh()
        owner.bind(inner, NUMBER)
        owner.bind(outer, array(inner), closed=True)
        pipe = ProjectionPipeline(owner, CATALOG)
        result = pipe.materialize(indexed(pipe, outer))
        self.assertEqual(pipe.display(result), repr(NUMBER))
        expect(pipe, result, NUMBER)
        owner.grow(inner, STRING)
        self.assertTrue(ShapeQuery("sub", NUMBER, NUMBER, CATALOG).holds(owner.snapshot))
        with self.assertRaises(Invalid):
            pipe.close()

    def test_outer_shape_change_is_not_hidden_by_closed_outer_alias(self):
        owner = Owner()
        outer, shape = owner.fresh(), owner.fresh()
        owner.bind(shape, tup(NUMBER))
        owner.bind(outer, shape, closed=True)
        pipe = ProjectionPipeline(owner, CATALOG)
        result = indexed(pipe, outer)
        expect(pipe, result, NUMBER)
        owner.grow(shape, tup(STRING))
        with self.assertRaises(Invalid):
            pipe.close()

    def test_tuple_length_growth_with_same_projection_remains_valid(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, tup(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        result = indexed(pipe, shape)
        expect(pipe, result, NUMBER)
        owner.grow(shape, tup(NUMBER, NUMBER))
        self.assertEqual(pipe.display(result), repr(NUMBER))
        pipe.close()

    def test_nested_alias_projection_keeps_binder_identity(self):
        owner = Owner()
        v = owner.fresh()
        pipe = ProjectionPipeline(owner, CATALOG)
        twice = alias(ELEMENTS, alias(ELEMENTS, array(array(v))))
        value = pipe.instantiate(pipe.source(twice))
        self.assertEqual(pipe.display(value), repr(v))
        owner.bind(v, STRING)
        expect(pipe, value, STRING)
        pipe.close()

    def test_distinct_declarations_with_same_spelling_do_not_share_cache(self):
        catalog = Catalog((Definition("one.ts#Same/0", 0, array(NUMBER)),
                           Definition("two.ts#Same/0", 0, array(STRING))))
        pipe = ProjectionPipeline(Owner(), catalog)
        left = pipe.project(pipe.expand(pipe.source(alias("one.ts#Same/0"))))
        right = pipe.project(pipe.expand(pipe.source(alias("two.ts#Same/0"))))
        self.assertEqual(pipe.display(left), repr(NUMBER))
        self.assertEqual(pipe.display(right), repr(STRING))
        expect(pipe, left, NUMBER)
        expect(pipe, right, STRING)
        pipe.close()

    def test_catalog_is_immutable_input_not_ambient_name_resolution(self):
        a = Catalog((Definition("x#A", 0, array(NUMBER)),))
        b = Catalog((Definition("x#A", 0, array(STRING)),))
        owner = Owner()
        source = alias("x#A")
        self.assertNotEqual(ShapeQuery("projectable", source, BOTTOM, a),
                            ShapeQuery("projectable", source, BOTTOM, b))
        proposal = ProjectionPipeline(owner, a).probe(source)
        with self.assertRaises(Misuse):
            ProjectionPipeline(owner, b).replay(proposal)

    def test_pipeline_does_not_offer_a_catalog_or_owner_replacement_operation(self):
        pipe = ProjectionPipeline(Owner(), CATALOG)
        with self.assertRaises(AttributeError):
            pipe.catalog = Catalog()
        with self.assertRaises(AttributeError):
            pipe.owner = Owner()

    def test_clone_only_shape_cannot_authorize_parent(self):
        owner = Owner()
        shape = owner.fresh()
        pipe = ProjectionPipeline(owner, CATALOG)
        before = owner.snapshot
        proposal = pipe.probe(shape, lambda c: c.bind(shape, array(NUMBER)))
        self.assertIn("number", proposal.preview)
        self.assertEqual(owner.snapshot, before)
        with self.assertRaises(Blocked):
            pipe.replay(proposal)
        with self.assertRaises(Blocked):
            pipe.close()

    def test_parent_replay_recomputes_instead_of_copying_preview(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, array(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        proposal = pipe.probe(shape, lambda c: c.seal(shape))
        owner.grow(shape, array(STRING))
        value = pipe.replay(proposal)
        self.assertEqual(pipe.display(value), repr(join(NUMBER, STRING)))
        expect(pipe, value, join(NUMBER, STRING))
        pipe.close()

    def test_nonmutating_probe_is_not_a_future_type_guarantee(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, array(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        value = pipe.replay(pipe.probe(shape))
        expect(pipe, value, NUMBER)
        owner.grow(shape, array(STRING))
        with self.assertRaises(Invalid):
            pipe.close()

    def test_probe_failure_does_not_add_parent_requirements(self):
        owner = Owner()
        shape = owner.fresh()
        pipe = ProjectionPipeline(owner, CATALOG)
        self.assertIn("blocked", pipe.probe(shape).preview)
        pipe.close()

    def test_failed_projection_remains_pending(self):
        owner = Owner()
        shape = owner.fresh()
        pipe = ProjectionPipeline(owner, CATALOG)
        with self.assertRaises(Blocked):
            indexed(pipe, shape)
        with self.assertRaises(Blocked):
            pipe.close()

    def test_bad_union_arm_cannot_be_silently_dropped(self):
        pipe = ProjectionPipeline(Owner(), CATALOG)
        with self.assertRaises(Blocked):
            indexed(pipe, join(array(NUMBER), STRING))
        with self.assertRaises(Blocked):
            pipe.close()

    def test_failed_alias_operation_is_registered_before_expansion(self):
        pipe = ProjectionPipeline(Owner(), CATALOG)
        source = pipe.source(NUMBER)
        with self.assertRaises(Blocked):
            pipe.expand(source)
        with self.assertRaises(Blocked):
            pipe.close()

    def test_opaque_parameter_cannot_be_projected_as_its_bound(self):
        pipe = ProjectionPipeline(Owner(), CATALOG)
        with self.assertRaises(Blocked):
            indexed(pipe, atom("rigid:T"))
        with self.assertRaises(Blocked):
            pipe.close()

    def test_symbolic_rigid_elements_preserve_their_identity(self):
        pipe = ProjectionPipeline(Owner(), CATALOG)
        t = atom("rigid:T")
        result = indexed(pipe, array(t))
        expect(pipe, result, t)
        with self.assertRaises(Invalid):
            expect(pipe, result, NUMBER)
        with self.assertRaises(Invalid):
            pipe.close()

    def test_source_scope_rejects_even_erased_private_candidate(self):
        owner = Owner()
        child = owner._fork()
        private = child.fresh()
        catalog = Catalog((Definition("Ignore", 1, NUMBER),))
        pipe = ProjectionPipeline(owner, catalog)
        with self.assertRaises(Blocked):
            pipe.source(alias("Ignore", private))
        with self.assertRaises(Blocked):
            pipe.close()

    def test_recursive_alias_is_blocked_not_accepted_coinductively(self):
        catalog = Catalog((Definition("Loop", 0, alias("Loop")),))
        pipe = ProjectionPipeline(Owner(), catalog)
        with self.assertRaises(Blocked):
            pipe.source(alias("Loop"))
        with self.assertRaises(Blocked):
            pipe.close()

    def test_recursive_candidate_is_outside_the_fragment(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, array(v), closed=True)
        pipe = ProjectionPipeline(owner, CATALOG)
        with self.assertRaises(Blocked):
            indexed(pipe, v)
        with self.assertRaises(Blocked):
            pipe.close()

    def test_cache_hits_reuse_receipts_without_growing_journal(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        pipe = ProjectionPipeline(owner, CATALOG)
        source = pipe.source(alias(ELEMENTS, array(v)))
        value = pipe.instantiate(source)
        ticket = owner.finish()
        evaluations = owner.evaluations
        for _ in range(1000):
            self.assertEqual(pipe.instantiate(source), value)
        self.assertEqual(owner.evaluations, evaluations)
        self.assertEqual(owner.finish().obligations, ticket.obligations)
        self.assertEqual(len(pipe._entries), 3)  # Source, alias expansion, projection.
        self.assertEqual(pipe.cache_hits, 2000)

    def test_cache_hit_after_unrelated_growth_replays_original_premises(self):
        owner = Owner()
        v, unrelated = owner.fresh(), owner.fresh()
        owner.bind(v, NUMBER)
        owner.bind(unrelated, NUMBER)
        pipe = ProjectionPipeline(owner, CATALOG)
        source = pipe.source(alias(ELEMENTS, array(v)))
        value = pipe.instantiate(source)
        previous = owner.evaluations
        owner.grow(unrelated, STRING)
        self.assertEqual(pipe.instantiate(source), value)
        self.assertGreater(owner.evaluations, previous)
        expect(pipe, value, NUMBER)
        pipe.close()

    def test_cache_hit_must_not_drop_new_input_provenance(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, array(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        ground = pipe.source(array(NUMBER))
        cached = pipe.project(ground)
        frozen = pipe.materialize(pipe.source(shape))
        result = pipe.project(frozen)  # Same cache key, additional premise.
        self.assertGreater(len(pipe._entries[result._identity].prerequisites),
                           len(pipe._entries[cached._identity].prerequisites))
        owner.grow(shape, array(STRING))
        with self.assertRaises(Invalid):
            pipe.display(result)
        with self.assertRaises(Invalid):
            pipe.close()

    def test_rolled_back_cache_entry_is_recomputed_not_resurrected(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, array(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        source = pipe.source(shape)
        saved = owner.save()
        discarded = pipe.project(source)
        owner.restore(saved)
        with self.assertRaises(Misuse):
            pipe.display(discarded)
        fresh = pipe.project(source)
        self.assertNotEqual(discarded, fresh)
        expect(pipe, fresh, NUMBER)
        pipe.close()

    def test_rollback_removes_failed_path_and_all_its_prerequisites(self):
        owner = Owner()
        shape = owner.fresh()
        owner.bind(shape, array(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        source = pipe.source(shape)
        saved = owner.save()
        owner.grow(shape, array(STRING))
        with self.assertRaises(Invalid):
            expect(pipe, pipe.project(source), NUMBER)
        owner.restore(saved)
        expect(pipe, pipe.project(source), NUMBER)
        pipe.close()

    def test_composition_retains_both_input_derivations(self):
        owner = Owner()
        a, b = owner.fresh(), owner.fresh()
        owner.bind(a, array(NUMBER))
        owner.bind(b, array(NUMBER))
        pipe = ProjectionPipeline(owner, CATALOG)
        value = pipe.combine(indexed(pipe, a), indexed(pipe, b))
        expect(pipe, value, NUMBER)
        owner.grow(b, array(STRING))
        with self.assertRaises(Invalid):
            pipe.display(value)
        with self.assertRaises(Invalid):
            pipe.close()

    def test_handles_are_bound_to_their_pipeline(self):
        p, q = ProjectionPipeline(Owner(), CATALOG), ProjectionPipeline(Owner(), CATALOG)
        value = p.source(NUMBER)
        with self.assertRaises(Misuse):
            q.display(value)
        with self.assertRaises(Misuse):
            p.display(Derived(value._identity, object()))
        with self.assertRaises(Misuse):
            p.display(replace(value, _identity=999999))

    def test_publication_retires_owner_and_preserves_readonly_receipts(self):
        owner = Owner()
        v = owner.fresh()
        owner.bind(v, NUMBER)
        pipe = ProjectionPipeline(owner, CATALOG)
        value = indexed(pipe, array(v))
        expect(pipe, value, NUMBER)
        accepted = pipe.close()
        self.assertEqual(pipe.display(value), repr(v))
        with self.assertRaises(Misuse):
            owner.grow(v, STRING)
        owner.publish(accepted)

    def test_empty_tuple_and_union_of_known_shapes(self):
        pipe = ProjectionPipeline(Owner(), CATALOG)
        empty = indexed(pipe, tup())
        self.assertEqual(pipe.display(empty), repr(BOTTOM))
        mixed = indexed(pipe, join(tup(NUMBER), tup(STRING, NUMBER), array(NUMBER)))
        expect(pipe, mixed, join(NUMBER, STRING))
        pipe.close()

    def test_finite_shape_oracle(self):
        # Independent set-of-element-labels oracle, not evaluate() as expected.
        samples = [
            (tup(), set()), (tup(NUMBER), {"number"}),
            (array(NUMBER), {"number"}), (array(STRING), {"string"}),
            (tup(NUMBER, STRING), {"number", "string"}),
        ]
        checked = 0
        for (initial, labels), (growth, extra), nested, mode in product(
            samples, samples, (False, True), ("normal", "frozen", "sealed")
        ):
            owner = Owner()
            shape = owner.fresh()
            owner.bind(shape, initial, closed=(mode == "sealed"))
            original = shape
            if nested:
                outer = owner.fresh()
                owner.bind(outer, shape, closed=True)
                original = outer
            if mode == "frozen":
                owner.set_mode("frozen")
            pipe = ProjectionPipeline(owner, CATALOG)
            value = indexed(pipe, original)
            expected_old = join(*(atom(x) for x in labels))
            self.assertEqual(pipe.display(value), repr(expected_old))
            expect(pipe, value, expected_old)
            before = owner.snapshot
            owner.finish()
            self.assertEqual(owner.snapshot, before)
            owner.grow(shape, growth)
            expected_new = labels | extra if mode == "normal" else labels
            try:
                pipe.close()
                accepted = True
            except Invalid:
                accepted = False
            self.assertEqual(accepted, expected_new == labels,
                             (initial, growth, nested, mode))
            checked += 1
        self.assertEqual(checked, 150)


if __name__ == "__main__":
    unittest.main()
