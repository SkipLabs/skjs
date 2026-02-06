type ObjectWithReadonlyField = {
  readonly ro: number;
  mut: number;
};

function writesOnReadonlyAndMutableFields(x: ObjectWithReadonlyField): void {
  // @skjs-expect-error Invalid assignment
  x.ro = 1;
  x.mut = 2;
}

type ObjectWithReadonlyOptionalField = {
  readonly opt?: number;
};

function writesOnReadonlyOptionalField(x: ObjectWithReadonlyOptionalField): void {
  // @skjs-expect-error Invalid assignment
  x.opt = 3;
}

type ObjectWithReadonlyIndex = {
  readonly [k: string]: number;
};

function writesOnReadonlyIndex(x: ObjectWithReadonlyIndex): void {
  // @skjs-expect-error Invalid assignment
  x["a"] = 1;
  // @skjs-expect-error Invalid assignment
  x.b = 2;
}

type UnionReadonlyAndMutable = { readonly a: number } | { a: number };

function writeOnUnionReadonlyAndMutable(x: UnionReadonlyAndMutable): void {
  // @skjs-expect-error Invalid assignment
  x.a = 1;
}

type NestedReadonlyObject = {
  readonly cfg: {
    readonly port: number;
  };
};

function nestedReadonlyObjectWritesAreRejected(x: NestedReadonlyObject): void {
  // @skjs-expect-error Invalid assignment
  x.cfg = { port: 2 };
  // @skjs-expect-error Invalid assignment
  x.cfg.port = 3;
}

type NestedMutableObject = {
  cfg: {
    port: number;
  };
};

function nestedMutableObjectWritesAreAccepted(x: NestedMutableObject): void {
  x.cfg = { port: 2 };
  x.cfg.port = 3;
}
