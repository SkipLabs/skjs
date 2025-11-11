function unsupportedConsoleApis(): void {
  // @ts-expect-error Unbound field: table
  console.table("data");
}
