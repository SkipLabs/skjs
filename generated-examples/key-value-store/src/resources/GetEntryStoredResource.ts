import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  KvEntry,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetEntryStoredResourceInputs extends SharedCollections {
  readonly entries: EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_>;
}

export class GetEntryStoredResource implements Resource<GetEntryStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetEntryStoredResourceInputs,
    _context: Context,
  ): EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_> {
    return inputs.entries;
  }
}
