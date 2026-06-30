import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { AppointmentsByResourceResource } from "./resources/AppointmentsByResourceResource.js";
import { GetAppointmentResource } from "./resources/GetAppointmentResource.js";
import { GetResourceResource } from "./resources/GetResourceResource.js";
import { GetUserByIdResource } from "./resources/GetUserByIdResource.js";
import { ListAppointmentsResource } from "./resources/ListAppointmentsResource.js";
import { ListAvailabilityWindowsResource } from "./resources/ListAvailabilityWindowsResource.js";
import { ListResourcesResource } from "./resources/ListResourcesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  AvailabilityWindowKey,
  AvailabilityWindowStored,
  BookableResource_skip_id_,
  BookableResource_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetUserParams,
  ListAppointmentsParams,
  ListAvailabilityParams,
  ListResourcesParams,
  Appointment,
  BookableResource,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly appointments: InputDefinition<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
  readonly availabilityWindows: InputDefinition<
    AvailabilityWindowKey,
    AvailabilityWindowStored
  >;
  readonly resources: InputDefinition<
    BookableResource_skip_id_,
    BookableResource_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly appointmentsByResourceResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly getAppointmentResource: ResourceClass<GraphCollections, Json>;
  readonly getResourceResource: ResourceClass<GraphCollections, Json>;
  readonly getUserByIdResource: ResourceClass<GraphCollections, GetUserParams>;
  readonly listAppointmentsResource: ResourceClass<
    GraphCollections,
    ListAppointmentsParams
  >;
  readonly listAvailabilityWindowsResource: ResourceClass<
    GraphCollections,
    ListAvailabilityParams
  >;
  readonly listResourcesResource: ResourceClass<
    GraphCollections,
    ListResourcesParams
  >;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      appointments: new InputDefinition<
        Appointment_skip_id_,
        Appointment_skip_value_
      >([]),
      availabilityWindows: new InputDefinition<
        AvailabilityWindowKey,
        AvailabilityWindowStored
      >([]),
      resources: new InputDefinition<
        BookableResource_skip_id_,
        BookableResource_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      appointmentsByResourceResource: AppointmentsByResourceResource,
      getAppointmentResource: GetAppointmentResource,
      getResourceResource: GetResourceResource,
      getUserByIdResource: GetUserByIdResource,
      listAppointmentsResource: ListAppointmentsResource,
      listAvailabilityWindowsResource: ListAvailabilityWindowsResource,
      listResourcesResource: ListResourcesResource,
      getMeResource: getMeResource,
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
