"""Three protocol counterexamples, NOT new runtime witnesses against SKJS."""
from model import Blocked, Invalid, NUMBER, STRING, Owner, Query, Ty, tup

owner = Owner()
x = owner.fresh()
proposal = owner.probe(Query("sub", NUMBER, x), lambda child: child.bind(x, NUMBER))
print(f"Clone-only solution: probe preview = {proposal.preview}")
try:
    owner.replay(proposal)
except Blocked as e:
    print(f"  Parent validation: BLOCKED ({e})")

owner = Owner()
x = owner.fresh()
owner.bind(x, NUMBER)
view = owner.observe(Ty("element", (tup(x),)))
owner.require(Query("sub", view.value, NUMBER))
owner.grow(x, STRING)
print(f"Copied output: frozen downstream check = {Query('sub', view.value, NUMBER).holds(owner.snapshot)}")
try:
    owner.finish()
except Invalid:
    print("  Retained source-normalization obligation: REJECTED")

owner = Owner()
x = owner.fresh()
start = owner.save()
owner.bind(x, NUMBER)
version, stamp = owner.legacy_version, owner.snapshot.stamp
owner.restore(start)
owner.bind(x, STRING)
print(f"Rollback/regrowth: numeric version repeats = {version == owner.legacy_version}")
print(f"  Snapshot identity repeats = {stamp == owner.snapshot.stamp}")
