class Foo {
  async bar(): Promise<number> {
    return 1;
  }
}

async function foo(): Promise<number> {
  return await new Foo().bar();
}

function makeAsyncClosure(): () => Promise<number> {
  return async (): Promise<number> => 0;
}

function makeAsyncClosure(): () => Promise<number> {
  return async () => 0;
}

function makeAsyncClosure(): () => Promise<number> {
  return async () => {
    return 0;
  };
}

function makeAsyncClosure(): () => Promise<number> {
  return async (): Promise<number> => {
    return 0;
  };
}
