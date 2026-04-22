// One type parameter's bound can refer to another; both are solved together
// from the argument type.
interface Ref<T> {
  contents: T;
}

function get<U, T extends Ref<U>>(x: T & object): U {
  return x.contents;
}

function main(): string {
  return get({ contents: "yo" });
}
