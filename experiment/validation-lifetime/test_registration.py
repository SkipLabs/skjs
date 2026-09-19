"""A required operation is journaled before evaluation, including blocked ones."""
import unittest
from model import BOTTOM, NUMBER, Blocked, Owner, Ty


class RegistrationTests(unittest.TestCase):
    def test_blocked_materialization_prevents_publication(self):
        owner = Owner()
        candidate = owner.fresh()
        with self.assertRaises(Blocked):
            owner.observe(Ty("element", (candidate,)))
        with self.assertRaises(Blocked):
            owner.close()

    def test_unsupported_materialization_prevents_publication(self):
        owner = Owner()
        with self.assertRaises(Blocked):
            owner.observe(Ty("unsupported", (NUMBER,)))
        with self.assertRaises(Blocked):
            owner.close()

    def test_rollback_discards_abandoned_materialization_request(self):
        owner = Owner()
        saved = owner.save()
        with self.assertRaises(Blocked):
            owner.observe(Ty("unsupported", (BOTTOM,)))
        owner.restore(saved)
        owner.close()

    def test_resolved_request_can_be_retried_without_sealing(self):
        owner = Owner()
        candidate = owner.fresh()
        with self.assertRaises(Blocked):
            owner.observe(candidate)
        owner.bind(candidate, NUMBER)
        self.assertEqual(owner.consume(owner.observe(candidate)), NUMBER)
        self.assertFalse(dict(owner.snapshot.bindings)[candidate.label].closed)
        owner.close()


if __name__ == "__main__":
    unittest.main()
