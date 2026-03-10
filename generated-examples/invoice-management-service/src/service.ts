import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  InvoiceId,
  InvoiceValue,
  LineItemId,
  LineItemValue,
  CustomerId,
  CustomerValue,
  DraftSentPaidOverdueEnum,
  InvoicesLineItemsResourceParams,
  CustomersInvoicesResourceParams,
} from "./types.js";


export type Inputs = {
  invoices: InputDefinition<InvoiceId, InvoiceValue>;
  lineItems: InputDefinition<LineItemId, LineItemValue>;
  customers: InputDefinition<CustomerId, CustomerValue>;
};

export type InputCollections = {
  invoices: EagerCollection<InvoiceId, InvoiceValue>;
  lineItems: EagerCollection<LineItemId, LineItemValue>;
  customers: EagerCollection<CustomerId, CustomerValue>;
};

export type GraphCollections = {
  invoices: EagerCollection<InvoiceId, InvoiceValue>;
  lineItems: EagerCollection<LineItemId, LineItemValue>;
  customers: EagerCollection<CustomerId, CustomerValue>;
};

export type Resources = {
  readonly "invoices": ResourceClass<GraphCollections, {}>;
  readonly "invoices-draft": ResourceClass<GraphCollections, {}>;
  readonly "invoices-sent": ResourceClass<GraphCollections, {}>;
  readonly "invoices-paid": ResourceClass<GraphCollections, {}>;
  readonly "invoices-overdue": ResourceClass<GraphCollections, {}>;
  readonly "invoices-lineItems": ResourceClass<GraphCollections, InvoicesLineItemsResourceParams>;
  readonly "customers-invoices": ResourceClass<GraphCollections, CustomersInvoicesResourceParams>;
};

export class InvoiceStatusFilterMapper implements Mapper<InvoiceId, InvoiceValue, InvoiceId, InvoiceValue> {
  private status: DraftSentPaidOverdueEnum;

  constructor(status: DraftSentPaidOverdueEnum) {
    this.status = status;
  }

  mapEntry(
    key: InvoiceId,
    values: Values<InvoiceValue>,
    _context: Context
  ): Iterable<[InvoiceId, InvoiceValue]> {
    const result: Array<[InvoiceId, InvoiceValue]> = Array.of();
    for (const v of values) {
      if (v.status === this.status) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class LineItemsByInvoiceFilterMapper implements Mapper<LineItemId, LineItemValue, LineItemId, LineItemValue> {
  private invoiceId: string;

  constructor(invoiceId: string) {
    this.invoiceId = invoiceId;
  }

  mapEntry(
    key: LineItemId,
    values: Values<LineItemValue>,
    _context: Context
  ): Iterable<[LineItemId, LineItemValue]> {
    const result: Array<[LineItemId, LineItemValue]> = Array.of();
    for (const v of values) {
      if (v.invoiceId === this.invoiceId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class InvoicesByCustomerFilterMapper implements Mapper<InvoiceId, InvoiceValue, InvoiceId, InvoiceValue> {
  private customerId: string;

  constructor(customerId: string) {
    this.customerId = customerId;
  }

  mapEntry(
    key: InvoiceId,
    values: Values<InvoiceValue>,
    _context: Context
  ): Iterable<[InvoiceId, InvoiceValue]> {
    const result: Array<[InvoiceId, InvoiceValue]> = Array.of();
    for (const v of values) {
      if (v.customerId === this.customerId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class InvoicesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices;
  }
}

export class InvoicesDraftResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "draft");
  }
}

export class InvoicesSentResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "sent");
  }
}

export class InvoicesPaidResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "paid");
  }
}

export class InvoicesOverdueResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "overdue");
  }
}

export class InvoicesLineItemsResource implements Resource<GraphCollections> {
  private invoiceId: string;

  constructor(params: InvoicesLineItemsResourceParams) {
    this.invoiceId = params.invoiceId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LineItemId, LineItemValue> {
    return cs.lineItems.map(LineItemsByInvoiceFilterMapper, this.invoiceId);
  }
}

export class CustomersInvoicesResource implements Resource<GraphCollections> {
  private customerId: string;

  constructor(params: CustomersInvoicesResourceParams) {
    this.customerId = params.customerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoicesByCustomerFilterMapper, this.customerId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                this.inputs = { invoices: new InputDefinition<InvoiceId, InvoiceValue>([]), lineItems: new InputDefinition<LineItemId, LineItemValue>([]), customers: new InputDefinition<CustomerId, CustomerValue>([]) };
    this.resources = { "invoices": InvoicesResource, "invoices-draft": InvoicesDraftResource, "invoices-sent": InvoicesSentResource, "invoices-paid": InvoicesPaidResource, "invoices-overdue": InvoicesOverdueResource, "invoices-lineItems": InvoicesLineItemsResource, "customers-invoices": CustomersInvoicesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { invoices: inputs.invoices, lineItems: inputs.lineItems, customers: inputs.customers };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
