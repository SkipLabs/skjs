// File that exports a unique symbol for import testing

// @skjs-expect-error TODO uniqueSymbol
export const exportedUniqueSymbol: unique symbol = Symbol("exported");

// Regular symbol export for comparison
export const regularSymbol: symbol = Symbol("regular");
