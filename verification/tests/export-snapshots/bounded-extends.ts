function asBoolean<T extends boolean>(x: T): boolean {
  return x;
}

function dependent<T, U extends T, V extends U>(x: V): V {
  return x;
}

// No declaration identifies this intersection with one rigid parameter.
function unrelated<T, U>(x: T & U): T & U {
  return x;
}

// Additional narrowing is not the declaration's original bound.
function narrower<T extends boolean, U extends T>(x: U & false): U & false {
  return x;
}
