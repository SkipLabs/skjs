import type { Lesson_skip_id_, Lesson_skip_value_, Lesson } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetLessonResourceInputs extends SharedCollections {
  readonly lessons: EagerCollection<Lesson_skip_id_, Lesson_skip_value_>;
}

export class GetLessonResource implements Resource<GetLessonResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetLessonResourceInputs,
    _context: Context,
  ): EagerCollection<Lesson_skip_id_, Lesson_skip_value_> {
    return inputs.lessons;
  }
}
