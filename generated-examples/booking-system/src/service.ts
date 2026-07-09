import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { AppointmentsByCustomerResource } from "./resources/AppointmentsByCustomerResource.js";
import { AppointmentsByProviderResource } from "./resources/AppointmentsByProviderResource.js";
import { AppointmentsByServiceResource } from "./resources/AppointmentsByServiceResource.js";
import { GetAppointmentResource } from "./resources/GetAppointmentResource.js";
import { GetServiceResource } from "./resources/GetServiceResource.js";
import { ListServicesResource } from "./resources/ListServicesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  Service_skip_id_,
  Service_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListServicesParams,
  Appointment,
  Service,
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
  readonly appointments: InputDefinition<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
  readonly services: InputDefinition<Service_skip_id_, Service_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly appointmentsByCustomerResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly appointmentsByProviderResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly appointmentsByServiceResource: ResourceClass<GraphCollections, Json>;
  readonly getAppointmentResource: ResourceClass<GraphCollections, Json>;
  readonly getServiceResource: ResourceClass<GraphCollections, Json>;
  readonly listServicesResource: ResourceClass<
    GraphCollections,
    ListServicesParams
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
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      appointments: new InputDefinition<
        Appointment_skip_id_,
        Appointment_skip_value_
      >([]),
      services: new InputDefinition<Service_skip_id_, Service_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      appointmentsByCustomerResource: AppointmentsByCustomerResource,
      appointmentsByProviderResource: AppointmentsByProviderResource,
      appointmentsByServiceResource: AppointmentsByServiceResource,
      getAppointmentResource: GetAppointmentResource,
      getServiceResource: GetServiceResource,
      listServicesResource: ListServicesResource,
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
