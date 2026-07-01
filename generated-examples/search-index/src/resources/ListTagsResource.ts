import { FilterTagByPrefixMapper } from "../mappers/FilterTagByPrefixMapper.js";
import type {
  Tag_skip_id_,
  Tag_skip_value_,
  TagNameSortKey,
  ListTagsParams,
  Tag,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListTagsResourceInputs extends SharedCollections {
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
}

export class ListTagsResource implements Resource<ListTagsResourceInputs> {
  private readonly namePrefix: string | null;

  constructor(params: ListTagsParams) {
    this.namePrefix = params.namePrefix ?? null;
  }

  instantiate(
    inputs: ListTagsResourceInputs,
    _context: Context,
  ): EagerCollection<TagNameSortKey, Tag_skip_value_> {
    return inputs.tags.map(FilterTagByPrefixMapper, this.namePrefix);
  }
}
