import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Course_skip_id_, Course_skip_value_, Course } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each course entry, emit the entry unchanged when (the instructorId param is absent OR the entry's value's instructorId field equals the instructorId param) AND (the published param is absent OR the entry's value's published field equals the published param). Otherwise emit nothing.
export class FilterCoursesMapper implements Mapper<
  Course_skip_id_,
  Course_skip_value_,
  Course_skip_id_,
  Course_skip_value_
> {
  constructor(
    private instructorId: string | null,
    private published: boolean | null,
  ) {}

  mapEntry(
    key: Course_skip_id_,
    values: Values<Course_skip_value_>,
    context: Context,
  ): Iterable<[Course_skip_id_, Course_skip_value_]> {
    // > body
    const emits: [Course_skip_id_, Course_skip_value_][] = [];
    for (const value of values.toArray()) {
      const instructorMatches =
        this.instructorId === null || value.instructorId === this.instructorId;
      const publishedMatches =
        this.published === null || value.published === this.published;
      if (instructorMatches && publishedMatches) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
