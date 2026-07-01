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
  Json,
} from "@skipruntime/core";

export interface GetCommentResourceInputs extends SharedCollections {
  readonly commentsAssembled: EagerCollection<
    Comment_skip_id_,
    Comment_skip_value_
  >;
}

export class GetCommentResource implements Resource<GetCommentResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCommentResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, Comment_skip_value_> {
    return inputs.commentsAssembled;
  }
}
