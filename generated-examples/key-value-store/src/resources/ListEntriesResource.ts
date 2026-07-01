import { EntriesByUserMapper } from "../mappers/EntriesByUserMapper.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  UserId,
  EntriesByUserMapperOut,
  KvEntry,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListEntriesResourceInputs extends SharedCollections {
  readonly entries: EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_>;
}

export class ListEntriesResource implements Resource<ListEntriesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListEntriesResourceInputs,
    _context: Context,
  ): EagerCollection<UserId, EntriesByUserMapperOut> {
    const entriesByUser = inputs.entries.map(EntriesByUserMapper);
    return entriesByUser;
  }
}
