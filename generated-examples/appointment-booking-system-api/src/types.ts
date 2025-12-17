export type PendingConfirmed4egz6Enum = "cancelled" | "completed" | "confirmed" | "pending";

export type ClientId = string;

export type ClientValue = {
  name: string;
  email: string;
  phone: string | null;
};

export type Client = ClientValue & { id: ClientId };

export type ProviderId = string;

export type ProviderValue = {
  name: string;
  specialty: string;
  availableFrom: number;
  availableTo: number;
};

export type Provider = ProviderValue & { id: ProviderId };

export type ServiceId = string;

export type ServiceValue = {
  name: string;
  description: string;
  durationMinutes: number;
  price: number;
  providerId: string;
};

export type Service = ServiceValue & { id: ServiceId };

export type AppointmentId = string;

export type AppointmentValue = {
  clientId: string;
  serviceId: string;
  providerId: string;
  startTime: number;
  endTime: number;
  status: PendingConfirmed4egz6Enum;
};

export type Appointment = AppointmentValue & { id: AppointmentId };

export type ServicesByProviderResourceParams = {
  providerId: string;
};

export type AppointmentsByClientResourceParams = {
  clientId: string;
};

export type AppointmentsByProviderResourceParams = {
  providerId: string;
};
