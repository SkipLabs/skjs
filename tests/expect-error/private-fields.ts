// Positive tests for private class members.
// `protected` is silently accepted but treated as `public`, so positive
// access tests focus on `private`. Negative tests are added alongside
// enforcement.

class WithPrivate {
  private px: number = 1;

  inSameClass(): number {
    return this.px;
  }
}

class TwoInstancesOfSameClass {
  private px: number = 0;

  copyFrom(other: TwoInstancesOfSameClass): number {
    return other.px;
  }
}
