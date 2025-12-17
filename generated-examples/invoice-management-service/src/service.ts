import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "@skipruntime/core";

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


type Inputs = {
  invoices: Entry<InvoiceId, InvoiceValue>[];
  lineItems: Entry<LineItemId, LineItemValue>[];
  customers: Entry<CustomerId, CustomerValue>[];
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

type Resources = {
  "invoices": new (params: Json) => Resource<GraphCollections>;
  "invoices-draft": new (params: Json) => Resource<GraphCollections>;
  "invoices-sent": new (params: Json) => Resource<GraphCollections>;
  "invoices-paid": new (params: Json) => Resource<GraphCollections>;
  "invoices-overdue": new (params: Json) => Resource<GraphCollections>;
  "invoices-lineItems": new (params: Json) => Resource<GraphCollections>;
  "customers-invoices": new (params: Json) => Resource<GraphCollections>;
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
    const arr = values.toArray();
    const result: Array<[InvoiceId, InvoiceValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[LineItemId, LineItemValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[InvoiceId, InvoiceValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.customerId === this.customerId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class InvoicesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices;
  }
}

export class InvoicesDraftResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "draft");
  }
}

export class InvoicesSentResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "sent");
  }
}

export class InvoicesPaidResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoiceStatusFilterMapper, "paid");
  }
}

export class InvoicesOverdueResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as InvoicesLineItemsResourceParams;
    this.invoiceId = typed.invoiceId;
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

  constructor(params: Json) {
    const typed = params as CustomersInvoicesResourceParams;
    this.customerId = typed.customerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<InvoiceId, InvoiceValue> {
    return cs.invoices.map(InvoicesByCustomerFilterMapper, this.customerId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyInvoices: Entry<InvoiceId, InvoiceValue>[] = Array.of();
    const emptyLineItems: Entry<LineItemId, LineItemValue>[] = Array.of();
    const emptyCustomers: Entry<CustomerId, CustomerValue>[] = Array.of();
    this.initialData = { invoices: emptyInvoices, lineItems: emptyLineItems, customers: emptyCustomers };
    this.resources = { "invoices": InvoicesResource, "invoices-draft": InvoicesDraftResource, "invoices-sent": InvoicesSentResource, "invoices-paid": InvoicesPaidResource, "invoices-overdue": InvoicesOverdueResource, "invoices-lineItems": InvoicesLineItemsResource, "customers-invoices": CustomersInvoicesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { invoices: inputs.invoices, lineItems: inputs.lineItems, customers: inputs.customers };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
