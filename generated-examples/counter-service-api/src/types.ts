export type CounterAction = {
  amount: number;
};

export type CounterId = string;

export type CounterValue = {
  name: string;
  value: number;
};

export type Counter = CounterValue & { id: CounterId };
