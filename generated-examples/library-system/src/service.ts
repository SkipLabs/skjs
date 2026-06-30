import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { ActiveLoansByBookResource } from "./resources/ActiveLoansByBookResource.js";
import { GetBookResource } from "./resources/GetBookResource.js";
import { GetBookStoredResource } from "./resources/GetBookStoredResource.js";
import { GetLoanResource } from "./resources/GetLoanResource.js";
import { GetLoanStoredResource } from "./resources/GetLoanStoredResource.js";
import { ListBooksResource } from "./resources/ListBooksResource.js";
import { ListLoansResource } from "./resources/ListLoansResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Book_skip_id_,
  Book_skip_value_,
  Loan_skip_id_,
  Loan_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetBookParams,
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
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly books: InputDefinition<Book_skip_id_, Book_skip_value_>;
  readonly loans: InputDefinition<Loan_skip_id_, Loan_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly activeLoansByBookResource: ResourceClass<GraphCollections, Json>;
  readonly getBookResource: ResourceClass<GraphCollections, GetBookParams>;
  readonly getBookStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getLoanResource: ResourceClass<GraphCollections, GetLoanParams>;
  readonly getLoanStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listBooksResource: ResourceClass<GraphCollections, Json>;
  readonly listLoansResource: ResourceClass<GraphCollections, ListLoansParams>;
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
      books: new InputDefinition<Book_skip_id_, Book_skip_value_>([]),
      loans: new InputDefinition<Loan_skip_id_, Loan_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      activeLoansByBookResource: ActiveLoansByBookResource,
      getBookResource: GetBookResource,
      getBookStoredResource: GetBookStoredResource,
      getLoanResource: GetLoanResource,
      getLoanStoredResource: GetLoanStoredResource,
      listBooksResource: ListBooksResource,
      listLoansResource: ListLoansResource,
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
