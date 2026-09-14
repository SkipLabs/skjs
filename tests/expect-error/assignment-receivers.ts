function temporaryReceiver(make: () => { value: number }): number {
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  make().value = 1;
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  make().value += 1;
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  return make().value++;
}

function selectedReceiver(
  flag: boolean,
  left: { value: boolean },
  right: { value: boolean },
): boolean {
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  return ((flag ? left : right).value ||= true);
}

function optionalReceiver(box: { child: { value: number } } | null): void {
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  // @skjs-expect-error Property access is not allowed on this type
  box?.child.value = 1;
}
