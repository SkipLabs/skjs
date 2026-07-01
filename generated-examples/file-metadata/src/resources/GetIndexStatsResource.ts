import type { User_skip_id_, IndexStatsStored, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetIndexStatsResourceInputs extends SharedCollections {
  readonly indexStatsByOwner: EagerCollection<User_skip_id_, IndexStatsStored>;
}

export class GetIndexStatsResource implements Resource<GetIndexStatsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetIndexStatsResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, IndexStatsStored> {
    return inputs.indexStatsByOwner;
  }
}
