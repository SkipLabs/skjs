import { FilterCommentsMapper } from "../mappers/FilterCommentsMapper.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  ListCommentsParams,
  Comment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCommentsResourceInputs extends SharedCollections {
  readonly commentsAssembled: EagerCollection<
    Comment_skip_id_,
    Comment_skip_value_
  >;
}

export class ListCommentsResource implements Resource<ListCommentsResourceInputs> {
  private readonly authorId: string | null;
  private readonly parentCommentId: string | null;
  private readonly rootOnly: boolean | null;

  constructor(params: ListCommentsParams) {
    this.authorId = params.authorId ?? null;
    this.parentCommentId = params.parentCommentId ?? null;
    this.rootOnly = params.rootOnly ?? null;
  }

  instantiate(
    inputs: ListCommentsResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, Comment_skip_value_> {
    return inputs.commentsAssembled.map(
      FilterCommentsMapper,
      this.parentCommentId,
      this.rootOnly,
      this.authorId,
    );
  }
}
