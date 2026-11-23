// Regression test for the cold-check perf issue in #1092: every field of
// BigService has a type that is a generic alias instantiated over the same
// large interface, which used to re-expand that interface from scratch for
// each field. The repeated fields are intentional — they exercise the shared
// cross-substitution expansion cache. The expect-error case pins that sharing
// never conflates distinct instantiations of the same alias.
import type {
  EagerCollection,
  Json,
  ResourceClass,
  SharedCollections,
} from "@skipruntime/core";

export interface GraphCollections extends SharedCollections {
  readonly referralCodes: EagerCollection<string, Json>;
  readonly referrals: EagerCollection<string, Json>;
  readonly rewards: EagerCollection<string, Json>;
  readonly users: EagerCollection<string, Json>;
  readonly referralCodesByCode: EagerCollection<string, Json>;
  readonly referralsByCodeId: EagerCollection<string, Json>;
  readonly referralsByReferrer: EagerCollection<string, Json>;
  readonly rewardsByBeneficiary: EagerCollection<string, Json>;
}

export interface BigService {
  readonly r0: ResourceClass<GraphCollections, Json>;
  readonly r1: ResourceClass<GraphCollections, Json>;
  readonly r2: ResourceClass<GraphCollections, Json>;
  readonly r3: ResourceClass<GraphCollections, Json>;
  readonly r4: ResourceClass<GraphCollections, Json>;
  readonly r5: ResourceClass<GraphCollections, Json>;
  readonly r6: ResourceClass<GraphCollections, Json>;
  readonly r7: ResourceClass<GraphCollections, Json>;
}

// Constructor parameters are contravariant, so a Json-params class is
// assignable to a string-params class...
function widenParams(svc: BigService): ResourceClass<GraphCollections, string> {
  return svc.r0;
}

declare const narrow: ResourceClass<GraphCollections, string>;

// ...but not the other way around.
function narrowParamsNotWidened(): ResourceClass<GraphCollections, Json> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return narrow;
}
