import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Lesson_skip_id_,
  Lesson_skip_value_,
  Course_skip_id_,
  Lesson,
  Course,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each lesson entry, emit one output pair whose key is sourced from the entry's value's courseId field, paired with a Lesson value listing every required field explicitly: id sourced from the entry's key; courseId sourced from the entry's value's courseId field; title sourced from the entry's value's title field; orderIndex sourced from the entry's value's orderIndex field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field. Optional fields: content is present when the entry's value's content field is present, sourced from the entry's value's content field, absent otherwise; durationMinutes is present when the entry's value's durationMinutes field is present, sourced from the entry's value's durationMinutes field, absent otherwise. The original lesson id from the entry's key is re-injected into the value's id field so the downstream assemble consumer can reconstruct the full Lesson entity.
export class LessonByCourseWithIdMapper implements Mapper<
  Lesson_skip_id_,
  Lesson_skip_value_,
  Course_skip_id_,
  Lesson
> {
  mapEntry(
    key: Lesson_skip_id_,
    values: Values<Lesson_skip_value_>,
    context: Context,
  ): Iterable<[Course_skip_id_, Lesson]> {
    // > body
    const emits: [Course_skip_id_, Lesson][] = [];
    for (const value of values.toArray()) {
      const lesson: Lesson = {
        id: key,
        courseId: value.courseId,
        title: value.title,
        orderIndex: value.orderIndex,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.content !== undefined && { content: value.content }),
        ...(value.durationMinutes !== undefined && {
          durationMinutes: value.durationMinutes,
        }),
      };
      emits.push([value.courseId, lesson]);
    }
    return emits;
    // < body
  }
}
