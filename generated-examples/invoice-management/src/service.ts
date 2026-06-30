import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetInvoiceResource } from "./resources/GetInvoiceResource.js";
import { GetInvoiceStoredResource } from "./resources/GetInvoiceStoredResource.js";
import { GetLineItemResource } from "./resources/GetLineItemResource.js";
import { ListCustomersResource } from "./resources/ListCustomersResource.js";
import { ListLineItemsRawResource } from "./resources/ListLineItemsRawResource.js";
import { ListLineItemsResource } from "./resources/ListLineItemsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Customer_skip_id_,
  Customer_skip_value_,
  Invoice_skip_id_,
  InvoiceStored,
  LineItem_skip_id_,
  LineItemStored,
  User_skip_id_,
  UserStored,
  Customer,
  Invoice,
  LineItem,
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
  readonly customers: InputDefinition<Customer_skip_id_, Customer_skip_value_>;
  readonly invoices: InputDefinition<Invoice_skip_id_, InvoiceStored>;
  readonly lineItems: InputDefinition<LineItem_skip_id_, LineItemStored>;
  readonly users: InputDefinition<User_skip_id_, UserStored>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getInvoiceResource: ResourceClass<GraphCollections, Json>;
  readonly getInvoiceStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getLineItemResource: ResourceClass<GraphCollections, Json>;
  readonly listCustomersResource: ResourceClass<GraphCollections, Json>;
  readonly listLineItemsRawResource: ResourceClass<GraphCollections, Json>;
  readonly listLineItemsResource: ResourceClass<GraphCollections, Json>;
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
      customers: new InputDefinition<Customer_skip_id_, Customer_skip_value_>(
        [],
      ),
      invoices: new InputDefinition<Invoice_skip_id_, InvoiceStored>([]),
      lineItems: new InputDefinition<LineItem_skip_id_, LineItemStored>([]),
      users: new InputDefinition<User_skip_id_, UserStored>([]),
    };
    this.resources = {
      getInvoiceResource: GetInvoiceResource,
      getInvoiceStoredResource: GetInvoiceStoredResource,
      getLineItemResource: GetLineItemResource,
      listCustomersResource: ListCustomersResource,
      listLineItemsRawResource: ListLineItemsRawResource,
      listLineItemsResource: ListLineItemsResource,
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
