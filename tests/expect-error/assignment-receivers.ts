function temporaryReceiver(make: () => { value: number }): number {
  make().value = 1;
  make().value += 1;
  return make().value++;
}

function selectedReceiver(
  flag: boolean,
  left: { value: boolean },
  right: { value: boolean },
): boolean {
  return ((flag ? left : right).value ||= true);
}

function optionalReceiver(box: { child: { value: number } } | null): void {
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  // @skjs-expect-error Property access is not allowed on this type
  box?.child.value = 1;
}
