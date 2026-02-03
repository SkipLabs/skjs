// Type parameter inference from class constructor arguments.

class Holder<T> {
  constructor(public value: T) {}
}

// When Holder is instantiated with "hello", T is inferred as "hello".
// When T is "hello", holder.value has type "hello" and is not assignable to number.
function getNumber(): number {
  const holder = new Holder("hello");
  // @ts-expect-error Invalid return type
  return holder.value;
}

// Test with constrained type parameters.
// When T extends Constraint, the inferred type should unify with the argument type
// while respecting the constraint.

class Wrapper<T extends { required: string }> {
  item: T;
  constructor(item: T) {
    this.item = item;
  }

  getItem(): T {
    return this.item;
  }
}

function testConstrainedInference(): void {
  // Infer type arguments: passing { required: "yes", extra: 42 }
  // T should be inferred as the concrete type { required: string, extra: number }
  const w = new Wrapper({ required: "yes", extra: 42 });

  // Access the required field (present in constraint)
  // @skjs-expect-error Invalid access for type { required: ... }'0
  const req: string = w.item.required;

  // Access the extra field (only in concrete type, not in constraint)
  // TODO: This should work because T unified with the concrete type
  const extra: number = w.item.extra;

  // Same via method call
  const item = w.getItem();
  // TODO: This should also work
  const extra2: number = item.extra;
}

function testExplicitTypeArgs(): void {
  // With explicit type args, should work as expected
  const w = new Wrapper<{ required: string; extra: number }>({
    required: "yes",
    extra: 42,
  });

  const extra: number = w.item.extra;
}

// Test with multiple field constraints
class Container<T extends { id: number; name: string }> {
  data: T;
  constructor(d: T) {
    this.data = d;
  }
}

function testMultipleFields(): void {
  const c = new Container({ id: 1, name: "test", metadata: true });

  // @skjs-expect-error Invalid access for type { id: ..., name: ... }'0
  const id: number = c.data.id;
  // TODO: These should also work
  const name: string = c.data.name;
  const meta: boolean = c.data.metadata;
}
