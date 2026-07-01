import { FilterFileByIdAndOwnerMapper } from "../mappers/FilterFileByIdAndOwnerMapper.js";
import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  GetFileParams,
  FileRecord,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetFileResourceInputs extends SharedCollections {
  readonly files: EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_>;
}

export class GetFileResource implements Resource<GetFileResourceInputs> {
  private readonly fileId: string;
  private readonly userId: string;

  constructor(params: GetFileParams) {
    this.fileId = params.fileId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetFileResourceInputs,
    _context: Context,
  ): EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_> {
    return inputs.files.map(
      FilterFileByIdAndOwnerMapper,
      this.userId,
      this.fileId,
    );
  }
}
