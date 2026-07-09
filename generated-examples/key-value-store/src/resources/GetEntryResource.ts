import { FilterEntryByUserAndKeyMapper } from "../mappers/FilterEntryByUserAndKeyMapper.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  GetEntryParams,
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
  private readonly key: string;
  private readonly userId: string;

  constructor(params: GetEntryParams) {
    this.key = params.key;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetEntryResourceInputs,
    _context: Context,
  ): EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_> {
    return inputs.entries.map(
      FilterEntryByUserAndKeyMapper,
      this.userId,
      this.key,
    );
  }
}
