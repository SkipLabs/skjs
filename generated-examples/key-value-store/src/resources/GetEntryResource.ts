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
} from "@skipruntime/core";

export interface GetEntryResourceInputs extends SharedCollections {
  readonly entries: EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_>;
}

export class GetEntryResource implements Resource<GetEntryResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetEntryResourceInputs,
    _context: Context,
  ): EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_> {
    return inputs.entries;
  }
}
