import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  LessonKey,
  Lesson_skip_value_,
  Course_skip_id_,
  LessonByCourseValue,
  Lesson,
  Course,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each lesson entry, emit one output pair whose key is sourced from the entry's key's courseId field, paired with a new LessonByCourseValue value whose id field is sourced from the entry's key's id field, whose courseId field is sourced from the entry's key's courseId field, and whose title, content, position, createdAt, updatedAt fields are sourced from the corresponding fields of the entry's value.
export class LessonsByCourseMapper implements Mapper<
  LessonKey,
  Lesson_skip_value_,
  Course_skip_id_,
  LessonByCourseValue
> {
  mapEntry(
    key: LessonKey,
    values: Values<Lesson_skip_value_>,
    context: Context,
  ): Iterable<[Course_skip_id_, LessonByCourseValue]> {
    // > body
    const emits: [Course_skip_id_, LessonByCourseValue][] = [];
    for (const value of values.toArray()) {
      const out: LessonByCourseValue = {
        id: key.id,
        courseId: key.courseId,
        title: value.title,
        position: value.position,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.content !== undefined && { content: value.content }),
      };
      emits.push([key.courseId, out]);
    }
    return emits;
    // < body
  }
}
