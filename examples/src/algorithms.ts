// Array manipulation algorithms

function findMax(numbers: Array<number>): number {
    if (numbers.length === 0) {
        return 0;
    }
    
    let max = numbers[0];
    if (max === undefined) {
        return 0;
    }
    
    for (let i = 1; i < numbers.length; i++) {
        let current = numbers[i];
        if (current !== undefined && current > max) {
            max = current;
        }
    }
    return max;
}

function fibonacci(n: number): number {
    if (n <= 1) {
        return n;
    }
    return fibonacci(n - 1) + fibonacci(n - 2);
}

function createTestArray(): Array<number> {
    let result: Array<number> = new Array<number>();
    result.push(64);
    result.push(34);
    result.push(25);
    result.push(12);
    result.push(22);
    result.push(11);
    result.push(90);
    return result;
}

function factorial(n: number): number {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

function algorithmsDemo(): void {
    // Test the algorithms
    let testNumbers: Array<number> = createTestArray();
    console.log("Max value: " + findMax(testNumbers).toString());
    console.log("Fibonacci(10): " + fibonacci(10).toString());
    console.log("Factorial(5): " + factorial(5).toString());
}

algorithmsDemo();