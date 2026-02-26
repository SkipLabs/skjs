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
  ProductId,
  ProductValue,
  InventoryId,
  InventoryValue,
  ProductWithInventoryId,
  ProductWithInventoryValue,
  ProductsCategoryResourceParams,
} from "./types.js";

export type Inputs = {
  products: InputDefinition<ProductId, ProductValue>;
  inventory: InputDefinition<InventoryId, InventoryValue>;
};

export type InputCollections = {
  products: EagerCollection<ProductId, ProductValue>;
  inventory: EagerCollection<InventoryId, InventoryValue>;
};

export type GraphCollections = {
  productsWithInventory: EagerCollection<ProductWithInventoryId, ProductWithInventoryValue>;
};

export type Resources = {
  "products": ResourceClass<GraphCollections, {}>;
  "products-category": ResourceClass<GraphCollections, ProductsCategoryResourceParams>;
  "inventory-low-stock": ResourceClass<GraphCollections, {}>;
};

export class ProductInventoryJoinMapper implements Mapper<ProductId, ProductValue, ProductWithInventoryId, ProductWithInventoryValue> {
  private inventory: EagerCollection<InventoryId, InventoryValue>;

  constructor(inventory: EagerCollection<InventoryId, InventoryValue>) {
    this.inventory = inventory;
  }

  mapEntry(
    key: ProductId,
    values: Values<ProductValue>,
    _context: Context
  ): Iterable<[ProductWithInventoryId, ProductWithInventoryValue]> {
    const result: Array<[ProductWithInventoryId, ProductWithInventoryValue]> = Array.of();
    for (const product of values) {
      const inventoryArr = this.inventory.getArray(key);
      let quantity = 0;
      let reservedQuantity = 0;
      const inv = inventoryArr[0];
      if (inv !== undefined) {
        quantity = inv.quantity;
        reservedQuantity = inv.reservedQuantity;
      }
      const availableQuantity = quantity - reservedQuantity;
      const productWithInventory: ProductWithInventoryValue = {
        name: product.name,
        description: product.description,
        price: product.price,
        category: product.category,
        sku: product.sku,
        quantity: quantity,
        reservedQuantity: reservedQuantity,
        availableQuantity: availableQuantity
      };
      result.push([key, productWithInventory]);
    }
    return result;
  }
}

export class CategoryFilterMapper implements Mapper<ProductWithInventoryId, ProductWithInventoryValue, ProductWithInventoryId, ProductWithInventoryValue> {
  private categoryName: string;

  constructor(categoryName: string) {
    this.categoryName = categoryName;
  }

  mapEntry(
    key: ProductWithInventoryId,
    values: Values<ProductWithInventoryValue>,
    _context: Context
  ): Iterable<[ProductWithInventoryId, ProductWithInventoryValue]> {
    const result: Array<[ProductWithInventoryId, ProductWithInventoryValue]> = Array.of();
    for (const product of values) {
      if (product.category === this.categoryName) {
        result.push([key, product]);
      }
    }
    return result;
  }
}

export class LowStockFilterMapper implements Mapper<ProductWithInventoryId, ProductWithInventoryValue, ProductWithInventoryId, ProductWithInventoryValue> {
  constructor() {
  }

  mapEntry(
    key: ProductWithInventoryId,
    values: Values<ProductWithInventoryValue>,
    _context: Context
  ): Iterable<[ProductWithInventoryId, ProductWithInventoryValue]> {
    const result: Array<[ProductWithInventoryId, ProductWithInventoryValue]> = Array.of();
    for (const product of values) {
      if (product.availableQuantity <= 10) {
        result.push([key, product]);
      }
    }
    return result;
  }
}

export class ProductsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductWithInventoryId, ProductWithInventoryValue> {
    return cs.productsWithInventory;
  }
}

export class ProductsCategoryResource implements Resource<GraphCollections> {
  private categoryName: string;

  constructor(params: ProductsCategoryResourceParams) {
    this.categoryName = params.categoryName;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductWithInventoryId, ProductWithInventoryValue> {
    return cs.productsWithInventory.map(CategoryFilterMapper, this.categoryName);
  }
}

export class InventoryLowStockResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductWithInventoryId, ProductWithInventoryValue> {
    return cs.productsWithInventory.map(LowStockFilterMapper);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
            this.inputs = { products: new InputDefinition<ProductId, ProductValue>([]), inventory: new InputDefinition<InventoryId, InventoryValue>([]) };
    this.resources = { "products": ProductsResource, "products-category": ProductsCategoryResource, "inventory-low-stock": InventoryLowStockResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const productsWithInventory = inputs.products.map(ProductInventoryJoinMapper, inputs.inventory);
    return { productsWithInventory };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
