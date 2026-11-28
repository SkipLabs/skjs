// Branded primitive types (issue #630):
// `P & { readonly __brand: "Tag" }` / `P & { readonly [sym]: Tag }`
//
// Pre-change pinning test: primitive & non-boxing-object intersections
// currently collapse to `never`, making branded types uninhabited and
// causing downstream false positives / unsoundness (e.g., `UserId`
// assignable to `OrderId` and `number` because `never <: T`, while
// `.length`, `+`, and `as` construction fail).

declare const brandSym: unique symbol;

type UserId = string & { readonly __brand: "UserId" };
type OrderId = string & { readonly __brand: "OrderId" };
type ReverseOrderId = { readonly __brand: "ReverseOrderId" } & string;
type AdminUserId = UserId & { readonly __admin: true };
type OptionalBrandId = string & { readonly __brand?: "OptionalBrand" };
type PositiveInt = number & { readonly __brand: "PositiveInt" };
type BigId = bigint & { readonly __brand: "BigId" };
type Flag = boolean & { readonly __brand: "Flag" };
type Tagged<T, B> = T & { readonly [brandSym]: B };
type TaggedUser = Tagged<string, "User">;
type TaggedOrder = Tagged<string, "Order">;
type MultiFieldBrand = string & {
  readonly __brand: "Multi";
  readonly __version: 1;
};

declare function makeUserId(s: string): UserId;
declare function makeOrderId(s: string): OrderId;
declare function makePositiveInt(n: number): PositiveInt;
declare function makeBigId(b: bigint): BigId;
declare function makeFlag(b: boolean): Flag;
declare function makeTaggedUser(s: string): TaggedUser;
declare function makeTaggedOrder(s: string): TaggedOrder;
declare function makeAdminUserId(s: string): AdminUserId;
declare function makeReverseOrderId(s: string): ReverseOrderId;
declare function makeOptionalBrandId(s: string): OptionalBrandId;
declare function makeMultiFieldBrand(s: string): MultiFieldBrand;

// Construction via `as` cast from underlying primitive
function testCastUserId(s: string): UserId {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return s as UserId;
}

function testCastOrderId(s: string): OrderId {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return s as OrderId;
}

function testCastReverseOrderId(s: string): ReverseOrderId {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return s as ReverseOrderId;
}

function testCastOptionalBrandId(s: string): OptionalBrandId {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return s as OptionalBrandId;
}

function testCastPositiveInt(n: number): PositiveInt {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return n as PositiveInt;
}

function testCastTaggedUser(s: string): TaggedUser {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return s as TaggedUser;
}

function testCastMultiFieldBrand(s: string): MultiFieldBrand {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return s as MultiFieldBrand;
}

function testCastAdminUserId(uid: UserId): AdminUserId {
  // Currently `UserId` collapses to `never`, so `uid as AdminUserId` passes vacuously
  return uid as AdminUserId;
}

// Wrong-base `as` cast must still be rejected
function testWrongBaseCastNumber(n: number): UserId {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return n as UserId;
}

function testWrongBaseCastUnknown(u: unknown): UserId {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return u as UserId;
}

// Cross-brand `as` cast must be rejected (OrderId is not assignable to UserId via bare `as`)
function testCrossBrandCast(oid: OrderId): UserId {
  // Currently `OrderId` collapses to `never`, so `oid as UserId` silently succeeds!
  return oid as UserId;
}

// Upcasting branded type to underlying primitive
function testUpcastToBase(): void {
  const uid: UserId = makeUserId("u1");
  const s: string = uid;
  const rev: ReverseOrderId = makeReverseOrderId("r1");
  const s2: string = rev;
  const opt: OptionalBrandId = makeOptionalBrandId("o1");
  const s3: string = opt;
  const p: PositiveInt = makePositiveInt(42);
  const n: number = p;
  const b: BigId = makeBigId(1n);
  const bi: bigint = b;
  const f: Flag = makeFlag(true);
  const bl: boolean = f;
  const tu: TaggedUser = makeTaggedUser("tu1");
  const s4: string = tu;
  const aid: AdminUserId = makeAdminUserId("a1");
  const uidFromAdmin: UserId = aid;
  const s5: string = aid;
  const mf: MultiFieldBrand = makeMultiFieldBrand("m1");
  const s6: string = mf;
  const _use = [s, s2, s3, n, bi, bl, s4, uidFromAdmin, s5, s6];
}

// Assigning raw primitive to branded type must be rejected
function testPlainStringToUserId(s: string): UserId {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

function testPlainNumberToPositiveInt(n: number): PositiveInt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return n;
}

function testPlainStringToTaggedUser(s: string): TaggedUser {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

// Distinct brands must not be assignable to each other
function testUserIdToOrderId(uid: UserId): OrderId {
  // Currently collapses to `never`, so this unsoundly passes!
  return uid;
}

function testOrderIdToUserId(oid: OrderId): UserId {
  // Currently collapses to `never`, so this unsoundly passes!
  return oid;
}

function testTaggedUserToOrder(tu: TaggedUser): TaggedOrder {
  // Currently collapses to `never`, so this unsoundly passes!
  return tu;
}

function testTaggedOrderToUser(to: TaggedOrder): TaggedUser {
  // Currently collapses to `never`, so this unsoundly passes!
  return to;
}

function testUserIdToAdminUserId(uid: UserId): AdminUserId {
  // Currently collapses to `never`, so this unsoundly passes!
  return uid;
}

function testUserIdToNumber(uid: UserId): number {
  // Currently collapses to `never`, so this unsoundly passes!
  return uid;
}

// Primitive operations on branded values
function testStringMemberLength(): number {
  const uid: UserId = makeUserId("alice");
  // @skjs-expect-error Cannot access a property on type 'UserId'
  return uid.length;
}

function testStringMemberUpper(): string {
  const uid: UserId = makeUserId("alice");
  // @skjs-expect-error Cannot access a property on type 'UserId'
  return uid.toUpperCase();
}

function testStringEqualityAndTemplate(): void {
  const uid: UserId = makeUserId("alice");
  const uid2: UserId = makeUserId("bob");
  const _eq: boolean = uid === uid2;
  const _eqStr: boolean = uid === "alice";
  const _tpl: string = `user:${uid}`;
  // @skjs-expect-error Operator '+' cannot be applied to these types
  const _concat: string = uid + "-x";
  const _use = [_eq, _eqStr, _tpl, _concat];
}

function testNumberOps(): void {
  const p: PositiveInt = makePositiveInt(10);
  const p2: PositiveInt = makePositiveInt(20);
  // @skjs-expect-error Operator '+' cannot be applied to these types
  const _sum: number = p + p2;
  const _cmp: boolean = p < p2;
  const _neg: number = -p;
  const _use = [_sum, _cmp, _neg];
}

function testNumberMethod(): string {
  const p: PositiveInt = makePositiveInt(10);
  // @skjs-expect-error Cannot access a property on type 'PositiveInt'
  return p.toFixed(2);
}

function testBooleanOps(): boolean {
  const f: Flag = makeFlag(true);
  return !f;
}

function testBigIntOps(): bigint {
  const b: BigId = makeBigId(10n);
  // @skjs-expect-error Operator '+' cannot be applied to these types
  return b + 1n;
}

// Soundness: phantom brand fields must NOT be accessible on branded values!
function testBrandFieldNotAccessible(uid: UserId): unknown {
  // @skjs-expect-error Cannot access a property on type 'UserId'
  return uid.__brand;
}

function testSymbolBrandFieldNotAccessible(tu: TaggedUser): unknown {
  // @skjs-expect-error Cannot access a property on type 'TaggedUser'
  return tu[brandSym];
}

// Structural equality of identical brand definitions
type UserIdAlias = string & { readonly __brand: "UserId" };
function testStructuralBrandEquality(uid: UserId): UserId {
  const alias: UserIdAlias = uid;
  const back: UserId = alias;
  return back;
}

// Narrowing with typeof and unions
function testUnionAndNarrowing(x: UserId | number): string {
  if (typeof x === "string") {
    const uid: UserId = x;
    return uid;
  }
  const n: number = x;
  return n.toString();
}

// Non-brand intersection: string & { length: number } still simplifies to string
function testBoxedMemberIntersection(s: string): string {
  const x: string & { length: number } = s;
  return x;
}

// Generic function returning branded type
function identityBrand<T>(x: T): T {
  return x;
}
function testGenericRoundTrip(uid: UserId): UserId {
  return identityBrand(uid);
}

// Branded key in Record / object index
function testRecordWithBrandedKey(
  rec: Record<string, number>,
  uid: UserId,
): number | undefined {
  // @skjs-expect-error This type cannot be used as an index
  return rec[uid];
}
