function const_plus_const(): string {
  const a: "a" = "a" as const;
  const b: "b" = "b" as const;
  return a + b;
}
