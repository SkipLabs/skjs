// Test to verify that missing type annotations on anonymous function parameters produce errors

function testMissingAnnotations(): void {
  let numbers: Array<number> = new Array<number>();

  // @skjs-expect-error A parameter must have an explicit type annotation
  numbers.map((x) => x * 2);
}
