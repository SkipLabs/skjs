import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCustomerResource } from "./resources/GetCustomerResource.js";
import { GetCustomerStoredResource } from "./resources/GetCustomerStoredResource.js";
import { GetInvoiceResource } from "./resources/GetInvoiceResource.js";
import { GetInvoiceStoredResource } from "./resources/GetInvoiceStoredResource.js";
import { InvoicesByCustomerResource } from "./resources/InvoicesByCustomerResource.js";
import { ListCustomersResource } from "./resources/ListCustomersResource.js";
import { ListLineItemsRawResource } from "./resources/ListLineItemsRawResource.js";
import { ListLineItemsResource } from "./resources/ListLineItemsResource.js";
import { ListPaymentsRawResource } from "./resources/ListPaymentsRawResource.js";
import { ListPaymentsResource } from "./resources/ListPaymentsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Customer_skip_id_,
  CustomerStored,
  Invoice_skip_id_,
  InvoiceStored,
  LineItemKey,
  LineItemStored,
  PaymentKey,
  PaymentStored,
  User_skip_id_,
  User_skip_value_,
  ListCustomersParams,
  Customer,
  Invoice,
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
  readonly customers: InputDefinition<Customer_skip_id_, CustomerStored>;
  readonly invoices: InputDefinition<Invoice_skip_id_, InvoiceStored>;
  readonly lineItems: InputDefinition<LineItemKey, LineItemStored>;
  readonly payments: InputDefinition<PaymentKey, PaymentStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCustomerResource: ResourceClass<GraphCollections, Json>;
  readonly getCustomerStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getInvoiceResource: ResourceClass<GraphCollections, Json>;
  readonly getInvoiceStoredResource: ResourceClass<GraphCollections, Json>;
  readonly invoicesByCustomerResource: ResourceClass<GraphCollections, Json>;
  readonly listCustomersResource: ResourceClass<
    GraphCollections,
    ListCustomersParams
  >;
  readonly listLineItemsRawResource: ResourceClass<GraphCollections, Json>;
  readonly listLineItemsResource: ResourceClass<GraphCollections, Json>;
  readonly listPaymentsRawResource: ResourceClass<GraphCollections, Json>;
  readonly listPaymentsResource: ResourceClass<GraphCollections, Json>;
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
      customers: new InputDefinition<Customer_skip_id_, CustomerStored>([]),
      invoices: new InputDefinition<Invoice_skip_id_, InvoiceStored>([]),
      lineItems: new InputDefinition<LineItemKey, LineItemStored>([]),
      payments: new InputDefinition<PaymentKey, PaymentStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCustomerResource: GetCustomerResource,
      getCustomerStoredResource: GetCustomerStoredResource,
      getInvoiceResource: GetInvoiceResource,
      getInvoiceStoredResource: GetInvoiceStoredResource,
      invoicesByCustomerResource: InvoicesByCustomerResource,
      listCustomersResource: ListCustomersResource,
      listLineItemsRawResource: ListLineItemsRawResource,
      listLineItemsResource: ListLineItemsResource,
      listPaymentsRawResource: ListPaymentsRawResource,
      listPaymentsResource: ListPaymentsResource,
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
