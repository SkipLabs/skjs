function safeDivide(a: number, b: number): number {
  let attempts = 0;
  try {
    attempts = attempts + 1;
    if (b === 0) {
      throw new Error("division by zero");
    }
    return a / b;
  } catch (e) {
    return 0 - attempts;
  } finally {
    attempts = 0;
  }
}
