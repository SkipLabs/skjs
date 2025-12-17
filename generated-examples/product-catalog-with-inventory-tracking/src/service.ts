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
  ProductId,
  ProductValue,
  InventoryId,
  InventoryValue,
  ProductWithInventoryId,
  ProductWithInventoryValue,
  ProductsCategoryResourceParams,
} from "./types.js";

type Inputs = {
  products: Entry<ProductId, ProductValue>[];
  inventory: Entry<InventoryId, InventoryValue>[];
};

export type InputCollections = {
  products: EagerCollection<ProductId, ProductValue>;
  inventory: EagerCollection<InventoryId, InventoryValue>;
};

export type GraphCollections = {
  productsWithInventory: EagerCollection<ProductWithInventoryId, ProductWithInventoryValue>;
};

type Resources = {
  "products": new (params: Json) => Resource<GraphCollections>;
  "products-category": new (params: Json) => Resource<GraphCollections>;
  "inventory-low-stock": new (params: Json) => Resource<GraphCollections>;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const product = arr[i]!;
      const inventoryArr = this.inventory.getArray(key);
      let quantity = 0;
      let reservedQuantity = 0;
      if (inventoryArr.length > 0) {
        const inv = inventoryArr[0]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const product = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const product = arr[i]!;
      if (product.availableQuantity <= 10) {
        result.push([key, product]);
      }
    }
    return result;
  }
}

export class ProductsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as ProductsCategoryResourceParams;
    this.categoryName = typed.categoryName;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductWithInventoryId, ProductWithInventoryValue> {
    return cs.productsWithInventory.map(CategoryFilterMapper, this.categoryName);
  }
}

export class InventoryLowStockResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductWithInventoryId, ProductWithInventoryValue> {
    return cs.productsWithInventory.map(LowStockFilterMapper);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyProducts: Entry<ProductId, ProductValue>[] = Array.of();
    const emptyInventorys: Entry<InventoryId, InventoryValue>[] = Array.of();
    this.initialData = { products: emptyProducts, inventory: emptyInventorys };
    this.resources = { "products": ProductsResource, "products-category": ProductsCategoryResource, "inventory-low-stock": InventoryLowStockResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const productsWithInventory = inputs.products.map(ProductInventoryJoinMapper, inputs.inventory);
    return { productsWithInventory };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
