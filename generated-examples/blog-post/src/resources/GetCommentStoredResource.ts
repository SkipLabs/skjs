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

export interface GetCommentStoredResourceInputs extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
}

export class GetCommentStoredResource implements Resource<GetCommentStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCommentStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, Comment_skip_value_> {
    return inputs.comments;
  }
}
