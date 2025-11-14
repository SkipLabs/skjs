function unsupportedConsoleApis(): void {
  // @skjs-expect-error Unbound field: table
  console.table("data");
}
