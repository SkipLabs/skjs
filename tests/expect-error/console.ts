function unsupportedConsoleApis(): void {
  // @skjs-expect-error Property 'table' does not exist on this type
  console.table("data");
}
