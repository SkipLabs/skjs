// Math utility functions for sharing across modules

export function add(a: number, b: number): number {
    return a + b;
}

export function multiply(a: number, b: number): number {
    return a * b;
}

export function square(x: number): number {
    return x * x;
}

export function isEven(n: number): boolean {
    return n % 2 === 0;
}

export function isPositive(n: number): boolean {
    return n > 0;
}

export function factorial(n: number): number {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

export function fibonacci(n: number): number {
    if (n <= 1) {
        return n;
    }
    return fibonacci(n - 1) + fibonacci(n - 2);
}

export function gcd(a: number, b: number): number {
    if (b === 0) {
        return a;
    }
    return gcd(b, a % b);
}

export function isPrime(n: number): boolean {
    if (n < 2) {
        return false;
    }
    if (n === 2) {
        return true;
    }
    if (n % 2 === 0) {
        return false;
    }
    
    let limit = Math.floor(Math.sqrt(n));
    for (let i = 3; i <= limit; i = i + 2) {
        if (n % i === 0) {
            return false;
        }
    }
    return true;
}