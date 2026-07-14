async function createCounterService(): Promise<{
  createGraph(input: number): number;
}> {
  return {
    createGraph(input: number): number {
      return 0;
    },
  };
}
