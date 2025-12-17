import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

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

type Inputs = {
  clients: Entry<ClientId, ClientValue>[];
  providers: Entry<ProviderId, ProviderValue>[];
  services: Entry<ServiceId, ServiceValue>[];
  appointments: Entry<AppointmentId, AppointmentValue>[];
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

type Resources = {
  "clients": new (params: Json) => Resource<GraphCollections>;
  "providers": new (params: Json) => Resource<GraphCollections>;
  "services": new (params: Json) => Resource<GraphCollections>;
  "services-by-provider": new (params: Json) => Resource<GraphCollections>;
  "appointments": new (params: Json) => Resource<GraphCollections>;
  "appointments-by-client": new (params: Json) => Resource<GraphCollections>;
  "appointments-by-provider": new (params: Json) => Resource<GraphCollections>;
  "appointments-by-status-pending": new (params: Json) => Resource<GraphCollections>;
  "appointments-by-status-confirmed": new (params: Json) => Resource<GraphCollections>;
  "appointments-by-status-cancelled": new (params: Json) => Resource<GraphCollections>;
  "appointments-by-status-completed": new (params: Json) => Resource<GraphCollections>;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.status === this.status) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class ClientsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ClientId, ClientValue> {
    return cs.clients;
  }
}

export class ProvidersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProviderId, ProviderValue> {
    return cs.providers;
  }
}

export class ServicesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as ServicesByProviderResourceParams;
    this.providerId = typed.providerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ServiceId, ServiceValue> {
    return cs.services.map(FilterServicesByProviderMapper, this.providerId);
  }
}

export class AppointmentsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as AppointmentsByClientResourceParams;
    this.clientId = typed.clientId;
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

  constructor(params: Json) {
    const typed = params as AppointmentsByProviderResourceParams;
    this.providerId = typed.providerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByProviderMapper, this.providerId);
  }
}

export class AppointmentsByStatusPendingResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "pending" as AppointmentStatus);
  }
}

export class AppointmentsByStatusConfirmedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "confirmed" as AppointmentStatus);
  }
}

export class AppointmentsByStatusCancelledResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "cancelled" as AppointmentStatus);
  }
}

export class AppointmentsByStatusCompletedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AppointmentId, AppointmentValue> {
    return cs.appointments.map(FilterAppointmentsByStatusMapper, "completed" as AppointmentStatus);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyClients: Entry<ClientId, ClientValue>[] = Array.of();
    const emptyProviders: Entry<ProviderId, ProviderValue>[] = Array.of();
    const emptyServices: Entry<ServiceId, ServiceValue>[] = Array.of();
    const emptyAppointments: Entry<AppointmentId, AppointmentValue>[] = Array.of();
    this.initialData = { clients: emptyClients, providers: emptyProviders, services: emptyServices, appointments: emptyAppointments };
    this.resources = { "clients": ClientsResource, "providers": ProvidersResource, "services": ServicesResource, "services-by-provider": ServicesByProviderResource, "appointments": AppointmentsResource, "appointments-by-client": AppointmentsByClientResource, "appointments-by-provider": AppointmentsByProviderResource, "appointments-by-status-pending": AppointmentsByStatusPendingResource, "appointments-by-status-confirmed": AppointmentsByStatusConfirmedResource, "appointments-by-status-cancelled": AppointmentsByStatusCancelledResource, "appointments-by-status-completed": AppointmentsByStatusCompletedResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { clients: inputs.clients, providers: inputs.providers, services: inputs.services, appointments: inputs.appointments };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
