import { TagByNameLowerMapper } from "../mappers/TagByNameLowerMapper.js";
import type {
  Tag_skip_id_,
  Tag_skip_value_,
  TagNameLowerKey,
  Tag,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface TagByNameResourceInputs extends SharedCollections {
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
}

export class TagByNameResource implements Resource<TagByNameResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: TagByNameResourceInputs,
    _context: Context,
  ): EagerCollection<TagNameLowerKey, Tag> {
    return inputs.tags.map(TagByNameLowerMapper);
  }
}
