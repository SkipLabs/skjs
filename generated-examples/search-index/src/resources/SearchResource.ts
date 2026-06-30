import { FilterSearchDocMapper } from "../mappers/FilterSearchDocMapper.js";
import type { SearchSortKey, SearchDocument, SearchParams } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface SearchResourceInputs extends SharedCollections {
  readonly searchDocuments: EagerCollection<SearchSortKey, SearchDocument>;
}

export class SearchResource implements Resource<SearchResourceInputs> {
  private readonly authorId: string | null;
  private readonly q: string | null;
  private readonly tagName: string | null;

  constructor(params: SearchParams) {
    this.authorId = params.authorId ?? null;
    this.q = params.q ?? null;
    this.tagName = params.tagName ?? null;
  }

  instantiate(
    inputs: SearchResourceInputs,
    _context: Context,
  ): EagerCollection<SearchSortKey, SearchDocument> {
    return inputs.searchDocuments.map(
      FilterSearchDocMapper,
      this.q,
      this.tagName,
      this.authorId,
    );
  }
}
