import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { ActiveLoanCountByBookResource } from "./resources/ActiveLoanCountByBookResource.js";
import { GetBookResource } from "./resources/GetBookResource.js";
import { GetBookStoredResource } from "./resources/GetBookStoredResource.js";
import { GetLoanResource } from "./resources/GetLoanResource.js";
import { GetLoanStoredResource } from "./resources/GetLoanStoredResource.js";
import { GetMeResource } from "./resources/GetMeResource.js";
import { ListLoansResource } from "./resources/ListLoansResource.js";
import type {
  Book_skip_id_,
  BookStored,
  Loan_skip_id_,
  Loan_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetLoanParams,
  ListLoansParams,
  Book,
  Loan,
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
  readonly booksStored: InputDefinition<Book_skip_id_, BookStored>;
  readonly loans: InputDefinition<Loan_skip_id_, Loan_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly activeLoanCountByBookResource: ResourceClass<GraphCollections, Json>;
  readonly getBookResource: ResourceClass<GraphCollections, Json>;
  readonly getBookStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getLoanResource: ResourceClass<GraphCollections, GetLoanParams>;
  readonly getLoanStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
  readonly listLoansResource: ResourceClass<GraphCollections, ListLoansParams>;
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
      booksStored: new InputDefinition<Book_skip_id_, BookStored>([]),
      loans: new InputDefinition<Loan_skip_id_, Loan_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      activeLoanCountByBookResource: ActiveLoanCountByBookResource,
      getBookResource: GetBookResource,
      getBookStoredResource: GetBookStoredResource,
      getLoanResource: GetLoanResource,
      getLoanStoredResource: GetLoanStoredResource,
      getMeResource: GetMeResource,
      listLoansResource: ListLoansResource,
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
