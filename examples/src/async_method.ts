class Foo {
  async bar(): Promise<number> {
    return 1;
  }
}

async function foo(): Promise<number> {
  return await new Foo().bar();
}
