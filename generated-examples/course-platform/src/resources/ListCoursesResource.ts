import { FilterCoursesMapper } from "../mappers/FilterCoursesMapper.js";
import type {
  Course_skip_id_,
  Course_skip_value_,
  ListCoursesParams,
  Course,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCoursesResourceInputs extends SharedCollections {
  readonly courses: EagerCollection<Course_skip_id_, Course_skip_value_>;
}

export class ListCoursesResource implements Resource<ListCoursesResourceInputs> {
  private readonly instructorId: string | null;
  private readonly published: boolean | null;

  constructor(params: ListCoursesParams) {
    this.instructorId = params.instructorId ?? null;
    this.published = params.published ?? null;
  }

  instantiate(
    inputs: ListCoursesResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, Course_skip_value_> {
    return inputs.courses.map(
      FilterCoursesMapper,
      this.instructorId,
      this.published,
    );
  }
}
