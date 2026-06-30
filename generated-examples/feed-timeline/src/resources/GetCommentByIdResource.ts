import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Comment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetCommentByIdResourceInputs extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
}

export class GetCommentByIdResource implements Resource<GetCommentByIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetCommentByIdResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, Comment_skip_value_> {
    return inputs.comments;
  }
}
