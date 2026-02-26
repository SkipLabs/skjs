import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  ClientId,
  ClientValue,
  ProviderId,
  ProviderValue,
  ServiceId,
  ServiceValue,
  AppointmentId,
  AppointmentValue,
  PendingConfirmed4egz6Enum,
  ServicesByProviderResourceParams,
  AppointmentsByClientResourceParams,
  AppointmentsByProviderResourceParams,
} from "./types.js";

export type AppointmentStatus = PendingConfirmed4egz6Enum;

export type Inputs = {
  clients: InputDefinition<ClientId, ClientValue>;
  providers: InputDefinition<ProviderId, ProviderValue>;
  services: InputDefinition<ServiceId, ServiceValue>;
  appointments: InputDefinition<AppointmentId, AppointmentValue>;
};

export type InputCollections = {
  clients: EagerCollection<ClientId, ClientValue>;
  providers: EagerCollection<ProviderId, ProviderValue>;
  services: EagerCollection<ServiceId, ServiceValue>;
  appointments: EagerCollection<AppointmentId, AppointmentValue>;
};

export type GraphCollections = {
  clients: EagerCollection<ClientId, ClientValue>;
  providers: EagerCollection<ProviderId, ProviderValue>;
  services: EagerCollection<ServiceId, ServiceValue>;
  appointments: EagerCollection<AppointmentId, AppointmentValue>;
};

export type Resources = {
  "clients": ResourceClass<GraphCollections, {}>;
  "providers": ResourceClass<GraphCollections, {}>;
  "services": ResourceClass<GraphCollections, {}>;
  "services-by-provider": ResourceClass<GraphCollections, ServicesByProviderResourceParams>;
  "appointments": ResourceClass<GraphCollections, {}>;
  "appointments-by-client": ResourceClass<GraphCollections, AppointmentsByClientResourceParams>;
  "appointments-by-provider": ResourceClass<GraphCollections, AppointmentsByProviderResourceParams>;
  "appointments-by-status-pending": ResourceClass<GraphCollections, {}>;
  "appointments-by-status-confirmed": ResourceClass<GraphCollections, {}>;
  "appointments-by-status-cancelled": ResourceClass<GraphCollections, {}>;
  "appointments-by-status-completed": ResourceClass<GraphCollections, {}>;
};

export class FilterServicesByProviderMapper implements Mapper<ServiceId, ServiceValue, ServiceId, ServiceValue> {
  private providerId: string;

  constructor(providerId: string) {
    this.providerId = providerId;
  }

  mapEntry(
    key: ServiceId,
    values: Values<ServiceValue>,
    _context: Context
  ): Iterable<[ServiceId, ServiceValue]> {
    const result: Array<[ServiceId, ServiceValue]> = Array.of();
    for (const v of values) {
      if (v.providerId === this.providerId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterAppointmentsByClientMapper implements Mapper<AppointmentId, AppointmentValue, AppointmentId, AppointmentValue> {
  private clientId: string;

  constructor(clientId: string) {
    this.clientId = clientId;
  }

  mapEntry(
    key: AppointmentId,
    values: Values<AppointmentValue>,
    _context: Context
  ): Iterable<[AppointmentId, AppointmentValue]> {
    const result: Array<[AppointmentId, AppointmentValue]> = Array.of();
    for (const v of values) {
      if (v.clientId === this.clientId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterAppointmentsByProviderMapper implements Mapper<AppointmentId, AppointmentValue, AppointmentId, AppointmentValue> {
  private providerId: string;

  constructor(providerId: string) {
    this.providerId = providerId;
  }

  mapEntry(
    key: AppointmentId,
    values: Values<AppointmentValue>,
    _context: Context
  ): Iterable<[AppointmentId, AppointmentValue]> {
    const result: Array<[AppointmentId, AppointmentValue]> = Array.of();
    for (const v of values) {
      if (v.providerId === this.providerId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterAppointmentsByStatusMapper implements Mapper<AppointmentId, AppointmentValue, AppointmentId, AppointmentValue> {
  private status: AppointmentStatus;

  constructor(status: AppointmentStatus) {
    this.status = status;
  }

  mapEntry(
    key: AppointmentId,
    values: Values<AppointmentValue>,
    _context: Context
  ): Iterable<[AppointmentId, AppointmentValue]> {
    const result: Array<[AppointmentId, AppointmentValue]> = Array.of();
    for (const v of values) {
      if (v.status === this.status) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class ClientsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ClientId, ClientValue> {
    return cs.clients;
  }
}

export class ProvidersResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProviderId, ProviderValue> {
    return cs.providers;
  }
}

export class ServicesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ServiceId, ServiceValue> {
    return cs.services;
  }
}

export class ServicesByProviderResource implements Resource<GraphCollections> {
  private providerId: string;

  constructor(params: ServicesByProviderResourceParams) {
    this.providerId = params.providerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ServiceId, ServiceValue> {
    return cs.services.map(FilterServicesByProviderMapper, this.providerId);
  }
}

export class AppointmentsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments;
  }
}

export class AppointmentsByClientResource implements Resource<GraphCollections> {
  private clientId: string;

  constructor(params: AppointmentsByClientResourceParams) {
    this.clientId = params.clientId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByClientMapper, this.clientId);
  }
}

export class AppointmentsByProviderResource implements Resource<GraphCollections> {
  private providerId: string;

  constructor(params: AppointmentsByProviderResourceParams) {
    this.providerId = params.providerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByProviderMapper, this.providerId);
  }
}

export class AppointmentsByStatusPendingResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "pending");
  }
}

export class AppointmentsByStatusConfirmedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "confirmed");
  }
}

export class AppointmentsByStatusCancelledResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "cancelled");
  }
}

export class AppointmentsByStatusCompletedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "completed");
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
                    this.inputs = { clients: new InputDefinition<ClientId, ClientValue>([]), providers: new InputDefinition<ProviderId, ProviderValue>([]), services: new InputDefinition<ServiceId, ServiceValue>([]), appointments: new InputDefinition<AppointmentId, AppointmentValue>([]) };
    this.resources = { "clients": ClientsResource, "providers": ProvidersResource, "services": ServicesResource, "services-by-provider": ServicesByProviderResource, "appointments": AppointmentsResource, "appointments-by-client": AppointmentsByClientResource, "appointments-by-provider": AppointmentsByProviderResource, "appointments-by-status-pending": AppointmentsByStatusPendingResource, "appointments-by-status-confirmed": AppointmentsByStatusConfirmedResource, "appointments-by-status-cancelled": AppointmentsByStatusCancelledResource, "appointments-by-status-completed": AppointmentsByStatusCompletedResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { clients: inputs.clients, providers: inputs.providers, services: inputs.services, appointments: inputs.appointments };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
