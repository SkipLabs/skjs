import { FilterEntriesByPrefixMapper } from "../mappers/FilterEntriesByPrefixMapper.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  ListEntriesParams,
  KvEntry,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListEntriesResourceInputs extends SharedCollections {
  readonly entries: EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_>;
}

export class ListEntriesResource implements Resource<ListEntriesResourceInputs> {
  private readonly prefix: string | null;

  constructor(params: ListEntriesParams) {
    this.prefix = params.prefix ?? null;
  }

  instantiate(
    inputs: ListEntriesResourceInputs,
    _context: Context,
  ): EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_> {
    return inputs.entries.map(FilterEntriesByPrefixMapper, this.prefix);
  }
}
