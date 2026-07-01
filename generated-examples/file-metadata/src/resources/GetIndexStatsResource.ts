import { FileStatsContribMapper } from "../mappers/FileStatsContribMapper.js";
import { IndexStatsReducer } from "../reducers/IndexStatsReducer.js";
import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  StatsSingletonKey,
  IndexStatsAccum,
  GetIndexStatsParams,
  FileRecord,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetIndexStatsResourceInputs extends SharedCollections {
  readonly files: EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_>;
}

export class GetIndexStatsResource implements Resource<GetIndexStatsResourceInputs> {
  private readonly userId: string;

  constructor(params: GetIndexStatsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetIndexStatsResourceInputs,
    _context: Context,
  ): EagerCollection<StatsSingletonKey, IndexStatsAccum> {
    const contributions = inputs.files.map(FileStatsContribMapper, this.userId);
    return contributions.reduce(IndexStatsReducer);
  }
}
