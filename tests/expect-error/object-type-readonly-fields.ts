type ObjectWithReadonlyField = {
  readonly ro: number;
  mut: number;
};

function writesOnReadonlyAndMutableFields(x: ObjectWithReadonlyField): void {
  // FIXME: SKJS should reject this (readonly)
  x.ro = 1;
  x.mut = 2;
}

type ObjectWithReadonlyOptionalField = {
  readonly opt?: number;
};

function writesOnReadonlyOptionalField(
  x: ObjectWithReadonlyOptionalField,
): void {
  // FIXME: SKJS should reject this (readonly)
  x.opt = 3;
}

type ObjectWithReadonlyIndex = {
  readonly [k: string]: number;
};

function writesOnReadonlyIndex(x: ObjectWithReadonlyIndex): void {
  // FIXME: SKJS should reject this (readonly)
  x["a"] = 1;
  // FIXME: SKJS should reject this (readonly)
  x.b = 2;
}

type UnionReadonlyAndMutable = { readonly a: number } | { a: number };

function writeOnUnionReadonlyAndMutable(x: UnionReadonlyAndMutable): void {
  // FIXME: SKJS should reject this (readonly)
  x.a = 1;
}

type NestedReadonlyObject = {
  readonly cfg: {
    readonly port: number;
  };
};

function nestedReadonlyObjectWritesAreRejected(x: NestedReadonlyObject): void {
  // FIXME: SKJS should reject this (readonly)
  x.cfg = { port: 2 };
  // FIXME: SKJS should reject this (readonly)
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
