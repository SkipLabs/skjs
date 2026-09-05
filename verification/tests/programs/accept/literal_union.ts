function route(tag: "a" | "b" | "c", n: 1 | 2): string {
  if (tag === "a") {
    return "first";
  }
  if (n === 1) {
    return "one";
  }
  if (tag === "b") {
    return "second";
  }
  return "third";
}
