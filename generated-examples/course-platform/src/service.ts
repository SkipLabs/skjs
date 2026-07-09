import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCourseResource } from "./resources/GetCourseResource.js";
import { GetCourseStoredResource } from "./resources/GetCourseStoredResource.js";
import { GetEnrollmentResource } from "./resources/GetEnrollmentResource.js";
import { GetLessonResource } from "./resources/GetLessonResource.js";
import { GetUserResource } from "./resources/GetUserResource.js";
import { ListCoursesResource } from "./resources/ListCoursesResource.js";
import { ListEnrollmentsForCourseResource } from "./resources/ListEnrollmentsForCourseResource.js";
import { ListLessonsForCourseResource } from "./resources/ListLessonsForCourseResource.js";
import { ListMyEnrollmentsResource } from "./resources/ListMyEnrollmentsResource.js";
import type {
  Course_skip_id_,
  CourseStored,
  EnrollmentKey,
  Enrollment_skip_value_,
  Lesson_skip_id_,
  Lesson_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListCoursesParams,
  Course,
  Enrollment,
  Lesson,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly coursesStored: InputDefinition<Course_skip_id_, CourseStored>;
  readonly enrollments: InputDefinition<EnrollmentKey, Enrollment_skip_value_>;
  readonly lessons: InputDefinition<Lesson_skip_id_, Lesson_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCourseResource: ResourceClass<GraphCollections, Json>;
  readonly getCourseStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getEnrollmentResource: ResourceClass<GraphCollections, Json>;
  readonly getLessonResource: ResourceClass<GraphCollections, Json>;
  readonly getUserResource: ResourceClass<GraphCollections, Json>;
  readonly listCoursesResource: ResourceClass<
    GraphCollections,
    ListCoursesParams
  >;
  readonly listEnrollmentsForCourseResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listLessonsForCourseResource: ResourceClass<GraphCollections, Json>;
  readonly listMyEnrollmentsResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      coursesStored: new InputDefinition<Course_skip_id_, CourseStored>([]),
      enrollments: new InputDefinition<EnrollmentKey, Enrollment_skip_value_>(
        [],
      ),
      lessons: new InputDefinition<Lesson_skip_id_, Lesson_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCourseResource: GetCourseResource,
      getCourseStoredResource: GetCourseStoredResource,
      getEnrollmentResource: GetEnrollmentResource,
      getLessonResource: GetLessonResource,
      getUserResource: GetUserResource,
      listCoursesResource: ListCoursesResource,
      listEnrollmentsForCourseResource: ListEnrollmentsForCourseResource,
      listLessonsForCourseResource: ListLessonsForCourseResource,
      listMyEnrollmentsResource: ListMyEnrollmentsResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
