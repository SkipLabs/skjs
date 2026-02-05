type DepSafe = string | number | object;

// Core API expects variadic constructor
interface Collection {
  map<Params extends readonly DepSafe[]>(
    mapper: new (...params: Params) => { process(): void },
    ...params: Params
  ): void;
}

// ============================================
// CASE 1: Single parameter mapper
// ============================================

class SingleParamMapper {
  constructor(param: string) {}
  process(): void {}
}

declare const coll: Collection;

coll.map(SingleParamMapper, "hello");

// ============================================
// CASE 2: Multi-parameter mapper
// ============================================

class MultiParamMapper {
  constructor(_param1: string, _param2: number) {}
  process(): void {}
}

coll.map(MultiParamMapper, "hello", 42);

// ============================================
// NEGATIVE CASES: Wrong order / wrong arity
// ============================================

// Wrong order of args
// @ts-expect-error Invalid call
coll.map(MultiParamMapper, 42, "hello");

// Wrong number of args (missing required)
// @ts-expect-error Invalid call
coll.map(MultiParamMapper, "hello");

// Wrong number of args (extra arg)
// NOTE: tsc reports "Invalid call" here, but skjs is permissive with extra args
coll.map(SingleParamMapper, "hello", 42);
