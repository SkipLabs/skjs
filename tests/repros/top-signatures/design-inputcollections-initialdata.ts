// Design sketch: a sound API shape for named input collections + initial data.
//
// Model "named inputs" as per-collection wrappers that carry both:
// - a collection handle (EagerCollection<K,V>)
// - optional initial data for that collection (Entry<K,V>[])
//
// Key idea: keep the K/V association per field without relying on TS-only widening or on
// mapped/conditional/`infer` types to derive InitialData.
//
// ---------------------------------------------------------------------------
// Differences vs `import-stubs/@skipruntime/core/index.d.ts` (and motivation)
// ---------------------------------------------------------------------------
//
// 1) Named collections constraint
// - Stubs today: `NamedCollections = { [name: string]: EagerCollection<Json, Json> }`
//   This relies on unsound widening (treating a `EagerCollection<K,V>` as if it were
//   `EagerCollection<Json,Json>` even though `K` occurs in method parameter position).
// - This sketch: use a branded base type (`AbstractEagerCollection`) for the *record constraint*
//   (`NamedResourceCollections = { [name: string]: AbstractEagerCollection }`), while keeping
//   per-field `EagerCollection<K,V>` types intact on direct field access.
//
// 2) Initial data
// - Stubs today: `initialData?: InitialData<Inputs>` where `InitialData<...>` is a *separate*
//   service-level record of `Entry<K,V>[]` (coarsened to `Entry<Json,Json>[]` in the stubs).
//   Making it precise in TS typically wants mapped/conditional/`infer` types.
// - This sketch: move initial data next to its collection, in `InputCollection<K,V> { initial?: Entry<K,V>[] }`,
//   so the K/V association is preserved without type-level computation, and initial data can be present
//   per-collection (fine-grained).
//
// 3) Resource typing / output collections
// - Stubs today: `Resource<Collections extends NamedCollections>.instantiate(...) : EagerCollection<Json,Json>`,
//   which again widens away per-field K/V at the boundary.
// - This sketch: resources are typed against the concrete output record `ResourceInputs` and return
//   an `AbstractEagerCollection` (or more specific `EagerCollection<K,V>`), so K/V is not forced to Json/Json.
//
// IMPORTANT: "brand trick" motivation (TypeScript is structural).
// If base types were empty structural interfaces, many unrelated values (arrays/tuples/plain objects)
// would accidentally type-check as "collections". We use abstract base classes with protected brand
// fields to make these types effectively nominal: only actual collections/wrappers can inhabit them.
//
// This sketch matches the generated-service presentation:
// - a `class Service` implementing a service interface with `resources` + `createGraph`
// - input collections are wrapped (`InputCollection`) to carry optional initial data
// - output collections are plain `EagerCollection<K,V>` values (no wrapper), but the *record*
//   is still constrained via `NamedResourceCollections` (a branded base type)
//
// The bottom section includes several `@ts-expect-error` checks demonstrating that in a sound
// type system:
// - inputs/outputs must use the correct wrapper kind
// - per-collection initial data must match that collection's K/V
// - resources are typed against the output record and must return an actual collection
//
// Expected:
// - tsc: OK (expected errors are guarded by `@ts-expect-error`)
// - skjs: likely errors (classes / `extends` / etc. are still limited)

// ===================== FRAMEWORK SUBSET =====================

type Json =
    | null
    | boolean
    | number
    | string
    | object;

interface Context { }

// Nominal-ish base class so only real collections are assignable to the base type.
abstract class AbstractEagerCollection {
    protected __sk_collectionBrand!: void;
    protected constructor() { }
}

interface EagerCollection<K extends Json, V extends Json> extends AbstractEagerCollection {
    getArray(key: K): V[];
    getUnique(key: K): V;

    // Minimal "mapper" operation: mapping transforms one collection into another.
    // (The mapper operates on collections, not on any initial data carried in slots.)
    map<K2 extends Json, V2 extends Json>(mapper: Mapper<K, V, K2, V2>): EagerCollection<K2, V2>;
}

type Entry<K extends Json, V extends Json> = [K, V[]];

interface Mapper<
    K1 extends Json,
    V1 extends Json,
    K2 extends Json,
    V2 extends Json,
> {
    // Keep this minimal: enough to show "map takes a mapper and produces a new collection".
    // We don't care about the exact iterator protocol here.
    mapEntry(key: K1, values: V1[], context: Context): [K2, V2][];
}

// Input wrapper: collection + optional initial data.
abstract class AbstractInputCollection {
    protected __sk_inputSlotBrand!: void;
    protected constructor() { }
}

class InputCollection<K extends Json, V extends Json> extends AbstractInputCollection {
    public collection: EagerCollection<K, V>;
    public initial?: Entry<K, V>[];

    constructor(collection: EagerCollection<K, V>, initial?: Entry<K, V>[]) {
        super();
        this.collection = collection;
        this.initial = initial;
    }
}

type NamedInputCollections = { [name: string]: AbstractInputCollection };

type NamedResourceCollections = { [name: string]: AbstractEagerCollection };

export interface Resource<
    Collections extends NamedResourceCollections,
> {
    instantiate(
        collections: Collections,
        context: Context,
    ): AbstractEagerCollection;
}

interface SkipService<
    Inputs extends NamedInputCollections,
    ResourceInputs extends NamedResourceCollections,
> {
    resources: {
        [name: string]: new (params: Json) => Resource<ResourceInputs>;
    };

    createGraph(inputs: Inputs, context: Context): ResourceInputs;
}

// ========================= USER CODE =========================

type UserId = string;
type User = { name: string; tier: number };

type OrderId = number;
type Order = { total: number; userId: UserId };

type InputCollections = {
    users: InputCollection<UserId, User>;
    orders: InputCollection<OrderId, Order>;
};

type UserName = { name: string };

type OutputCollections = {
    // A derived graph collection produced by mapping over an input collection.
    // The key name is "collection-ish" and does NOT have to line up with resource names.
    userNamesById: EagerCollection<UserId, UserName>;
};

class UserToNameMapper implements Mapper<UserId, User, UserId, UserName> {
    mapEntry(key: UserId, values: User[], _context: Context): [UserId, UserName][] {
        // Minimal: map each user to just its name.
        return values.map((u) => [key, { name: u.name }]);
    }
}

class UserNamesResource implements Resource<OutputCollections> {
    instantiate(collections: OutputCollections, context: Context): EagerCollection<UserId, UserName> {
        return collections.userNamesById;
    }
}

class Service implements SkipService<InputCollections, OutputCollections> {
    public resources: {
        // Resource keys are independent from OutputCollections keys.
        "users": new (params: Json) => Resource<OutputCollections>;
        "debug-users": new (params: Json) => Resource<OutputCollections>;
    };

    constructor() {
        this.resources = {
            "users": UserNamesResource,
            "debug-users": UserNamesResource,
        };
    }

    createGraph(inputs: InputCollections, _context: Context): OutputCollections {
        // The mapper operates on the collection handle, not on the optional initial data.
        const userNamesCol = inputs.users.collection.map(new UserToNameMapper());
        return { userNamesById: userNamesCol };
    }
}

function service(): SkipService<InputCollections, OutputCollections> {
    return new Service();
}

declare const usersCol: EagerCollection<UserId, User>;
declare const ordersCol: EagerCollection<OrderId, Order>;
declare const ctx: Context;

// Provide initial data for just one collection (fine-grained / per-collection optionality).
const usersInitial: Entry<UserId, User>[] = [["u1", [{ name: "alice", tier: 1 }]]];

service().createGraph({ users: new InputCollection(usersCol, usersInitial), orders: new InputCollection(ordersCol) }, ctx);

// =================== NON-COLLECTIONS REJECTED ===================

type NotSlots = {
    todos: { title: string }[]; // <-- not an InputCollection wrapper
};

// This should be rejected by TypeScript: NotSlots does not satisfy
// `Inputs extends NamedInputCollections` (values must be branded AbstractInputCollection).
// @ts-expect-error NotSlots is not a record of AbstractInputCollection values.
type ShouldFail = SkipService<NotSlots, OutputCollections>;

// Wrong kind for outputs: outputs are plain EagerCollection values, not InputCollection wrappers.
type BadOutputs1 = {
    userNamesById: InputCollection<UserId, UserName>;
};

// @ts-expect-error BadOutputs1 does not satisfy `ResourceInputs extends NamedResourceCollections`.
type ShouldFailOutputs = SkipService<InputCollections, BadOutputs1>;

// Wrong kind for inputs: inputs must be InputCollection wrappers, not raw EagerCollection values.
type BadInputs1 = {
    users: EagerCollection<UserId, User>;
};

// @ts-expect-error BadInputs1 does not satisfy `Inputs extends NamedInputCollections`.
type ShouldFailInputs = SkipService<BadInputs1, OutputCollections>;

// Initial data must match the collection's K/V.
const wrongUsersInitialKey: Entry<number, User>[] = [[1, [{ name: "bob", tier: 2 }]]];
// @ts-expect-error Initial data key type must match UserId (= string).
const badUsersSlot1 = new InputCollection(usersCol, wrongUsersInitialKey);

const wrongUsersInitialValue: Entry<UserId, number>[] = [["u2", [123]]];
// @ts-expect-error Initial data value type must match User (= {name,tier}).
const badUsersSlot2 = new InputCollection(usersCol, wrongUsersInitialValue);

// A derived output collection must also match its declared K/V.
const badOutput: OutputCollections = {
    // @ts-expect-error OutputCollections.userNamesById expects UserId/UserName, not OrderId/Order.
    userNamesById: ordersCol,
};


