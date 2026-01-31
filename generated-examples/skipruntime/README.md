# skipruntime - Type-Safe Skip Service Bindings

A type-safe wrapper layer over `@skipruntime/core` and `@skipruntime/server` that provides sound typing for Skip reactive services.

## Problem

The standard `@skipruntime/core` bindings use unsound type widening. For example:

```typescript
// In @skipruntime/core, resources take untyped Json params
resources: {
  [name: string]: new (params: Json) => Resource<Collections>;
}
```

This forces developers to use unsafe casts inside resource constructors:

```typescript
constructor(params: Json) {
  const typed = params as MyParams;  // Unsafe cast!
  this.roomId = typed.roomId;
}
```

## Solution

This layer provides sound typing using two key techniques:

### 1. Branded Abstract Base Classes for Existential Types

Collections like `EagerCollection<K, V>` need to be stored heterogeneously (different K, V types in the same map). We model this using branded abstract base classes:

```typescript
// Branded base class representing ∃K,V. EagerCollection<K,V>
export abstract class AbstractEagerCollection {
  protected __sk_collectionBrand: undefined;
}

export interface EagerCollection<K extends Json, V extends Json>
  extends AbstractEagerCollection { ... }
```

The abstract base class acts as an existential type - it erases the type parameters while maintaining a distinct type identity.

### 2. The `never` Trick for Contravariant Parameters

Resources have typed constructor parameters, but we need to store different resource classes (with different param types) in a single map. We use `never` (the bottom type) to leverage contravariance:

```typescript
// ResourceClass captures the constructor signature
type ResourceClass<Collections, Params extends Json> =
  new (params: Params) => Resource<Collections>;

// In SkipService, use never for the params type
resources: {
  [name: string]: ResourceClass<ResourceInputs, never>;
}
```

This works because of function parameter contravariance:
- `never` extends every type
- So `new (params: SpecificType) => R` is assignable to `new (params: never) => R`

## Key Types

### InputDefinition<K, V>
Defines an input collection with its initial data and preserves type information:

```typescript
export class InputDefinition<K extends Json, V extends Json> {
  public initial: Entry<K, V>[];
  constructor(initial: Entry<K, V>[] = []) { ... }
}
```

### Resource<Collections>
Interface for resource classes that expose collections:

```typescript
export interface Resource<Collections extends NamedEagerCollections> {
  instantiate(collections: Collections, context: Context): AbstractEagerCollection;
}
```

### ResourceClass<Collections, Params>
Type representing a resource class with typed constructor:

```typescript
type ResourceClass<Collections, Params extends Json> =
  new (params: Params) => Resource<Collections>;
```

### SkipService<InputDefs, ResourceInputs>
The main service interface:

```typescript
interface SkipService<InputDefs, ResourceInputs> {
  inputs: InputDefs;
  resources: { [name: string]: ResourceClass<ResourceInputs, never> };
  createGraph(inputs: NamedEagerCollections, context: Context): ResourceInputs;
}
```

## Files

- **core.ts** - Type definitions (Entry, EagerCollection, Resource, SkipService, etc.)
- **server.ts** - Server adapter that wraps `@skipruntime/server` and extracts initial data from `InputDefinition`

## Usage

Services import from this shared layer instead of `@skipruntime/core`:

```typescript
import type { Resource, ResourceClass, SkipService } from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";
import { runService } from "../skipruntime/server.js";
```

Resource classes can now have typed constructors without casts:

```typescript
export class RoomsMessagesResource implements Resource<GraphCollections> {
  constructor(params: RoomsMessagesResourceParams) {  // Typed!
    this.roomId = params.roomId;  // No cast needed
  }
}
```

## Deriving Types in Tests

Tests can derive entry and param types from the service's exported types:

```typescript
import type { Inputs, Resources } from "./src/service.js";

// Derive input entry types
type InputEntries = {
  [K in keyof Inputs]: Inputs[K] extends InputDefinition<infer Key, infer Val>
    ? Entry<Key, Val>[]
    : never;
};

// Derive resource param types
type ResourceParams = {
  [K in keyof Resources]: Resources[K] extends ResourceClass<any, infer Params>
    ? Params
    : never;
};

// Usage
const users: InputEntries["users"] = [...];  // Type-safe!
const params: ResourceParams["rooms-messages"] = { roomId: "room1" };  // Type-safe!
```
