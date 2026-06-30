import { FilterFilesByOwnerMapper } from "../mappers/FilterFilesByOwnerMapper.js";
import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  ListFilesParams,
  FileRecord,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListFilesResourceInputs extends SharedCollections {
  readonly files: EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_>;
}

export class ListFilesResource implements Resource<ListFilesResourceInputs> {
  private readonly userId: string;

  constructor(params: ListFilesParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListFilesResourceInputs,
    _context: Context,
  ): EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_> {
    return inputs.files.map(FilterFilesByOwnerMapper, this.userId);
  }
}
