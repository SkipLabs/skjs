///////////////////////////////////////////////////////////////////////////////
// Comprehensive Algebraic Data Types Tests
// Tests ADT pattern matching, nested ADTs, and complex union types
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic ADT Pattern Matching
///////////////////////////////////////////////////////////////////////////////

type Color = 
    | { kind: 'red', intensity: number }
    | { kind: 'green', intensity: number }
    | { kind: 'blue', intensity: number };

function processColor(color: Color): string {
    if (color.kind === 'red') {
        return "Red with intensity: " + color.intensity.toString();
    } else if (color.kind === 'green') {
        return "Green with intensity: " + color.intensity.toString();
    } else if (color.kind === 'blue') {
        return "Blue with intensity: " + color.intensity.toString();
    }
    return "Unknown color";
}

function getColorIntensity(color: Color): number {
    if (color.kind === 'red') {
        return color.intensity;
    } else if (color.kind === 'green') {
        return color.intensity;
    } else if (color.kind === 'blue') {
        return color.intensity;
    }
    return 0;
}

///////////////////////////////////////////////////////////////////////////////
// Shape ADT with Different Field Types
///////////////////////////////////////////////////////////////////////////////

type Shape = 
    | { kind: 'circle', radius: number }
    | { kind: 'rectangle', width: number, height: number }
    | { kind: 'triangle', base: number, height: number, angles: number[] };

function calculateArea(shape: Shape): number {
    if (shape.kind === 'circle') {
        return 3.14159 * shape.radius * shape.radius;
    } else if (shape.kind === 'rectangle') {
        return shape.width * shape.height;
    } else if (shape.kind === 'triangle') {
        return 0.5 * shape.base * shape.height;
    }
    return 0;
}

function getShapePerimeter(shape: Shape): number {
    if (shape.kind === 'circle') {
        return 2 * 3.14159 * shape.radius;
    } else if (shape.kind === 'rectangle') {
        return 2 * (shape.width + shape.height);
    } else if (shape.kind === 'triangle') {
        return shape.base + shape.height + shape.base; // simplified
    }
    return 0;
}

function describeShape(shape: Shape): string {
    if (shape.kind === 'circle') {
        return "Circle with radius " + shape.radius.toString();
    } else if (shape.kind === 'rectangle') {
        return "Rectangle " + shape.width.toString() + "x" + shape.height.toString();
    } else if (shape.kind === 'triangle') {
        return "Triangle with base " + shape.base.toString() + " and height " + shape.height.toString();
    }
    return "Unknown shape";
}

///////////////////////////////////////////////////////////////////////////////
// Nested ADTs - Messages with Different Payloads
///////////////////////////////////////////////////////////////////////////////

type UserData = 
    | { kind: 'profile', name: string, email: string }
    | { kind: 'settings', theme: string, notifications: boolean }
    | { kind: 'activity', lastLogin: string, sessionCount: number };

type Message = 
    | { kind: 'text', content: string, timestamp: number }
    | { kind: 'user', userData: UserData, messageId: string }
    | { kind: 'system', level: string, code: number };

function processMessage(message: Message): string {
    if (message.kind === 'text') {
        return "Text: " + message.content + " at " + message.timestamp.toString();
    } else if (message.kind === 'user') {
        let userData = message.userData;
        if (userData.kind === 'profile') {
            return "User profile: " + userData.name + " (" + userData.email + ")";
        } else if (userData.kind === 'settings') {
            return "User settings: theme=" + userData.theme;
        } else if (userData.kind === 'activity') {
            return "User activity: " + userData.sessionCount.toString() + " sessions";
        }
        return "Unknown user data";
    } else if (message.kind === 'system') {
        return "System " + message.level + ": " + message.code.toString();
    }
    return "Unknown message";
}

function extractMessageId(message: Message): string {
    if (message.kind === 'text') {
        return "text-" + message.timestamp.toString();
    } else if (message.kind === 'user') {
        return message.messageId;
    } else if (message.kind === 'system') {
        return "system-" + message.code.toString();
    }
    return "unknown";
}

///////////////////////////////////////////////////////////////////////////////
// API Response ADT Pattern
///////////////////////////////////////////////////////////////////////////////

type ApiResult<T> = 
    | { kind: 'success', data: T, status: number }
    | { kind: 'error', message: string, code: number }
    | { kind: 'loading', progress: number };

function handleStringResult(result: ApiResult<string>): string {
    if (result.kind === 'success') {
        return "Success: " + result.data + " (status: " + result.status.toString() + ")";
    } else if (result.kind === 'error') {
        return "Error " + result.code.toString() + ": " + result.message;
    } else if (result.kind === 'loading') {
        return "Loading... " + result.progress.toString() + "%";
    }
    return "Unknown result";
}

function handleNumberResult(result: ApiResult<number>): string {
    if (result.kind === 'success') {
        return "Number result: " + result.data.toString();
    } else if (result.kind === 'error') {
        return "Failed to get number: " + result.message;
    } else if (result.kind === 'loading') {
        return "Loading number... " + result.progress.toString() + "%";
    }
    return "Unknown number result";
}

function isSuccessful<T>(result: ApiResult<T>): boolean {
    if (result.kind === 'success') {
        return true;
    }
    return false;
}

function getProgress<T>(result: ApiResult<T>): number {
    if (result.kind === 'loading') {
        return result.progress;
    }
    return 0;
}

///////////////////////////////////////////////////////////////////////////////
// State Machine ADT
///////////////////////////////////////////////////////////////////////////////

type ConnectionState = 
    | { kind: 'disconnected', reason: string }
    | { kind: 'connecting', timeout: number, attempts: number }
    | { kind: 'connected', sessionId: string, duration: number }
    | { kind: 'error', errorCode: number, retryAfter: number };

function transitionState(current: ConnectionState, action: string): ConnectionState {
    if (current.kind === 'disconnected') {
        if (action === 'connect') {
            return { kind: 'connecting', timeout: 5000, attempts: 1 };
        }
        return current;
    } else if (current.kind === 'connecting') {
        if (action === 'success') {
            return { kind: 'connected', sessionId: "session-123", duration: 0 };
        } else if (action === 'timeout') {
            return { kind: 'error', errorCode: 408, retryAfter: 3000 };
        }
        return current;
    } else if (current.kind === 'connected') {
        if (action === 'disconnect') {
            return { kind: 'disconnected', reason: "user_initiated" };
        }
        return current;
    } else if (current.kind === 'error') {
        if (action === 'retry') {
            return { kind: 'connecting', timeout: 5000, attempts: 1 };
        }
        return current;
    }
    return current;
}

function getStateDescription(state: ConnectionState): string {
    if (state.kind === 'disconnected') {
        return "Disconnected: " + state.reason;
    } else if (state.kind === 'connecting') {
        return "Connecting... attempt " + state.attempts.toString();
    } else if (state.kind === 'connected') {
        return "Connected with session " + state.sessionId;
    } else if (state.kind === 'error') {
        return "Error " + state.errorCode.toString() + ", retry after " + state.retryAfter.toString() + "ms";
    }
    return "Unknown state";
}

///////////////////////////////////////////////////////////////////////////////
// Tree Data Structure ADT
///////////////////////////////////////////////////////////////////////////////

type TreeNode<T> = 
    | { kind: 'leaf', value: T }
    | { kind: 'branch', left: TreeNode<T>, right: TreeNode<T>, value: T };

function countNodes<T>(tree: TreeNode<T>): number {
    if (tree.kind === 'leaf') {
        return 1;
    } else if (tree.kind === 'branch') {
        return 1 + countNodes(tree.left) + countNodes(tree.right);
    }
    return 0;
}

function sumNumberTree(tree: TreeNode<number>): number {
    if (tree.kind === 'leaf') {
        return tree.value;
    } else if (tree.kind === 'branch') {
        return tree.value + sumNumberTree(tree.left) + sumNumberTree(tree.right);
    }
    return 0;
}

function findInTree<T>(tree: TreeNode<T>, target: T): boolean {
    if (tree.kind === 'leaf') {
        // Note: We can't use === for generic types, so this is simplified
        return true; // Would need specific comparison logic
    } else if (tree.kind === 'branch') {
        return findInTree(tree.left, target) || findInTree(tree.right, target);
    }
    return false;
}

///////////////////////////////////////////////////////////////////////////////
// Option/Maybe ADT Pattern
///////////////////////////////////////////////////////////////////////////////

type Option<T> = 
    | { kind: 'some', value: T }
    | { kind: 'none' };

function mapOption<T, U>(option: Option<T>, fn: (value: T) => U): Option<U> {
    if (option.kind === 'some') {
        return { kind: 'some', value: fn(option.value) };
    } else if (option.kind === 'none') {
        return { kind: 'none' };
    }
    return { kind: 'none' };
}

function unwrapOption<T>(option: Option<T>, defaultValue: T): T {
    if (option.kind === 'some') {
        return option.value;
    } else if (option.kind === 'none') {
        return defaultValue;
    }
    return defaultValue;
}

function isSome<T>(option: Option<T>): boolean {
    if (option.kind === 'some') {
        return true;
    }
    return false;
}

function isNone<T>(option: Option<T>): boolean {
    if (option.kind === 'none') {
        return true;
    }
    return false;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Nested ADT with Arrays
///////////////////////////////////////////////////////////////////////////////

type DataValue = 
    | { kind: 'number', value: number }
    | { kind: 'text', value: string }
    | { kind: 'list', items: Array<DataValue> };

function processDataValue(data: DataValue): string {
    if (data.kind === 'number') {
        return "Number: " + data.value.toString();
    } else if (data.kind === 'text') {
        return "Text: " + data.value;
    } else if (data.kind === 'list') {
        return "List with " + data.items.length.toString() + " items";
    }
    return "Unknown data";
}

function countDataValues(data: DataValue): number {
    if (data.kind === 'number') {
        return 1;
    } else if (data.kind === 'text') {
        return 1;
    } else if (data.kind === 'list') {
        let count = 0;
        for (let i = 0; i < data.items.length; i++) {
            let item = data.items[i];
            if (item !== undefined) {
                count = count + countDataValues(item);
            }
        }
        return count;
    }
    return 0;
}

function extractNumbers(data: DataValue): Array<number> {
    let result: Array<number> = new Array<number>();
    
    if (data.kind === 'number') {
        result.push(data.value);
    } else if (data.kind === 'text') {
        // Do nothing for text
    } else if (data.kind === 'list') {
        for (let i = 0; i < data.items.length; i++) {
            let item = data.items[i];
            if (item !== undefined) {
                let itemNumbers = extractNumbers(item);
                for (let j = 0; j < itemNumbers.length; j++) {
                    let num = itemNumbers[j];
                    if (num !== undefined) {
                        result.push(num);
                    }
                }
            }
        }
    }
    
    return result;
}

///////////////////////////////////////////////////////////////////////////////
// Test Helper Functions
///////////////////////////////////////////////////////////////////////////////

function testBasicADTs(): void {
    let redColor: Color = { kind: 'red', intensity: 80 };
    let greenColor: Color = { kind: 'green', intensity: 60 };
    let blueColor: Color = { kind: 'blue', intensity: 90 };
    
    console.log(processColor(redColor));
    console.log(processColor(greenColor));
    console.log(processColor(blueColor));
    
    console.log(getColorIntensity(redColor).toString());
    console.log(getColorIntensity(greenColor).toString());
    console.log(getColorIntensity(blueColor).toString());
}

function testShapeADTs(): void {
    let circle: Shape = { kind: 'circle', radius: 5 };
    let rectangle: Shape = { kind: 'rectangle', width: 4, height: 6 };
    let angles: Array<number> = new Array<number>();
    angles.push(60);
    angles.push(60);
    angles.push(60);
    let triangle: Shape = { kind: 'triangle', base: 3, height: 4, angles: angles };
    
    console.log(calculateArea(circle).toString());
    console.log(calculateArea(rectangle).toString());
    console.log(calculateArea(triangle).toString());
    
    console.log(describeShape(circle));
    console.log(describeShape(rectangle));
    console.log(describeShape(triangle));
}

function testNestedADTs(): void {
    let profileData: UserData = { kind: 'profile', name: 'Alice', email: 'alice@example.com' };
    let settingsData: UserData = { kind: 'settings', theme: 'dark', notifications: true };
    let activityData: UserData = { kind: 'activity', lastLogin: '2024-01-01', sessionCount: 42 };
    
    let textMessage: Message = { kind: 'text', content: 'Hello World', timestamp: 1234567890 };
    let profileMessage: Message = { kind: 'user', userData: profileData, messageId: 'msg-001' };
    let systemMessage: Message = { kind: 'system', level: 'warning', code: 404 };
    
    console.log(processMessage(textMessage));
    console.log(processMessage(profileMessage));
    console.log(processMessage(systemMessage));
    
    console.log(extractMessageId(textMessage));
    console.log(extractMessageId(profileMessage));
    console.log(extractMessageId(systemMessage));
}

function testApiResults(): void {
    let successResult: ApiResult<string> = { kind: 'success', data: 'Hello', status: 200 };
    let errorResult: ApiResult<string> = { kind: 'error', message: 'Not found', code: 404 };
    let loadingResult: ApiResult<string> = { kind: 'loading', progress: 75 };
    
    console.log(handleStringResult(successResult));
    console.log(handleStringResult(errorResult));
    console.log(handleStringResult(loadingResult));
    
    console.log(isSuccessful(successResult).toString());
    console.log(isSuccessful(errorResult).toString());
    console.log(getProgress(loadingResult).toString());
}

function testStateMachine(): void {
    let disconnected: ConnectionState = { kind: 'disconnected', reason: 'timeout' };
    let connecting = transitionState(disconnected, 'connect');
    let connected = transitionState(connecting, 'success');
    let errorState = transitionState(connecting, 'timeout');
    
    console.log(getStateDescription(disconnected));
    console.log(getStateDescription(connecting));
    console.log(getStateDescription(connected));
    console.log(getStateDescription(errorState));
}

function testTreeADT(): void {
    let leaf1: TreeNode<number> = { kind: 'leaf', value: 10 };
    let leaf2: TreeNode<number> = { kind: 'leaf', value: 20 };
    let branch: TreeNode<number> = { kind: 'branch', left: leaf1, right: leaf2, value: 5 };
    
    console.log(countNodes(leaf1).toString());
    console.log(countNodes(branch).toString());
    console.log(sumNumberTree(leaf1).toString());
    console.log(sumNumberTree(branch).toString());
}

function doubleNumber(x: number): number {
    return x * 2;
}

function testOptionADT(): void {
    let someValue: Option<number> = { kind: 'some', value: 42 };
    let noneValue: Option<number> = { kind: 'none' };
    
    let mappedSome = mapOption(someValue, doubleNumber);
    let mappedNone = mapOption(noneValue, doubleNumber);
    
    console.log(isSome(someValue).toString());
    console.log(isNone(noneValue).toString());
    console.log(unwrapOption(someValue, 0).toString());
    console.log(unwrapOption(noneValue, 0).toString());
    
    if (mappedSome.kind === 'some') {
        console.log(mappedSome.value.toString());
    }
}

function testComplexNestedADT(): void {
    let numberData: DataValue = { kind: 'number', value: 42 };
    let textData: DataValue = { kind: 'text', value: 'hello' };
    
    let items: Array<DataValue> = new Array<DataValue>();
    items.push(numberData);
    items.push(textData);
    items.push({ kind: 'number', value: 100 });
    
    let listData: DataValue = { kind: 'list', items: items };
    
    console.log(processDataValue(numberData));
    console.log(processDataValue(textData));
    console.log(processDataValue(listData));
    
    console.log(countDataValues(listData).toString());
    
    let numbers = extractNumbers(listData);
    console.log(numbers.length.toString());
}

///////////////////////////////////////////////////////////////////////////////
// Elimination Refinement Tests
// Tests that type narrowing works by elimination in else branches
///////////////////////////////////////////////////////////////////////////////

type SimpleADT = 
    | { kind: 'a' }
    | { kind: 'b', msg: string };

function testSimpleElimination(value: SimpleADT): string {
    if (value.kind === 'a') {
        return "Found A";
    } else {
        // This should infer that value is { kind: 'b', msg: string }
        return "Found B: " + value.msg;
    }
}

type ThreeVariantADT = 
    | { kind: 'first', data: number }
    | { kind: 'second', info: string }
    | { kind: 'third', flag: boolean };

function testThreeVariantElimination(value: ThreeVariantADT): string {
    if (value.kind === 'first') {
        return "First: " + value.data.toString();
    } else if (value.kind === 'second') {
        return "Second: " + value.info;
    } else {
        // This should infer that value is { kind: 'third', flag: boolean }
        return "Third: " + value.flag.toString();
    }
}

type ComplexElimination = 
    | { kind: 'alpha', x: number, y: string }
    | { kind: 'beta', items: Array<number> }
    | { kind: 'gamma', nested: { a: boolean, b: number } }
    | { kind: 'delta', fn: (n: number) => string };

function testComplexElimination(value: ComplexElimination): string {
    if (value.kind === 'alpha') {
        return "Alpha: " + value.x.toString() + " - " + value.y;
    } else if (value.kind === 'beta') {
        return "Beta with " + value.items.length.toString() + " items";
    } else if (value.kind === 'gamma') {
        let nested = value.nested;
        return "Gamma: " + nested.a.toString() + ", " + nested.b.toString();
    } else {
        // This should infer that value is { kind: 'delta', fn: (n: number) => string }
        return "Delta: " + value.fn(42);
    }
}

type NestedElimination = 
    | { kind: 'outer', inner: { kind: 'inner1', val: number } | { kind: 'inner2', text: string } }
    | { kind: 'simple', value: boolean };

function testNestedElimination(value: NestedElimination): string {
    if (value.kind === 'outer') {
        let inner = value.inner;
        if (inner.kind === 'inner1') {
            return "Outer-Inner1: " + inner.val.toString();
        } else {
            // This should infer inner is { kind: 'inner2', text: string }
            return "Outer-Inner2: " + inner.text;
        }
    } else {
        // This should infer that value is { kind: 'simple', value: boolean }
        return "Simple: " + value.value.toString();
    }
}

type FourBranchADT = 
    | { kind: 'alpha', value: number, metadata: string }
    | { kind: 'beta', items: Array<string>, count: number }
    | { kind: 'gamma', flag: boolean, config: { enabled: boolean, timeout: number } }
    | { kind: 'delta', callback: (x: number) => boolean, priority: number };

type ChainedElimination = 
    | { kind: 'type1', a: number }
    | { kind: 'type2', b: string }
    | { kind: 'type3', c: boolean }
    | { kind: 'type4', d: Array<string> }
    | { kind: 'type5', e: { x: number, y: number } };

function testFourBranchElimination(value: FourBranchADT): string {
    if (value.kind === 'alpha') {
        return "Alpha: " + value.value.toString() + " (" + value.metadata + ")";
    } else if (value.kind === 'beta') {
        let firstItem = value.items[0];
        if (firstItem !== undefined) {
            return "Beta: " + value.count.toString() + " items, first=" + firstItem;
        } else {
            return "Beta: " + value.count.toString() + " items, first=undefined";
        }
    } else if (value.kind === 'gamma') {
        let config = value.config;
        return "Gamma: " + value.flag.toString() + ", enabled=" + config.enabled.toString() + ", timeout=" + config.timeout.toString();
    } else {
        // This should infer that value is { kind: 'delta', callback: (x: number) => boolean, priority: number }
        let result = value.callback(42);
        return "Delta: priority=" + value.priority.toString() + ", callback(42)=" + result.toString();
    }
}

function testFourBranchPartialElimination(value: FourBranchADT): string {
    // Test elimination after checking only one branch
    if (value.kind === 'alpha') {
        return "Found alpha: " + value.value.toString();
    } else {
        // Here value should be narrowed to beta | gamma | delta
        if (value.kind === 'beta') {
            return "Found beta with " + value.items.length.toString() + " items";
        } else {
            // Here value should be narrowed to gamma | delta
            if (value.kind === 'gamma') {
                return "Found gamma: " + value.flag.toString();
            } else {
                // This should infer that value is { kind: 'delta', callback: (x: number) => boolean, priority: number }
                return "Found delta with priority: " + value.priority.toString();
            }
        }
    }
}

function testFourBranchMiddleElimination(value: FourBranchADT): string {
    // Test elimination by checking middle branches first
    if (value.kind === 'beta') {
        return "Middle: Beta with " + value.count.toString() + " count";
    } else if (value.kind === 'gamma') {
        let config = value.config;
        return "Middle: Gamma timeout " + config.timeout.toString();
    } else {
        // Here value should be narrowed to alpha | delta
        if (value.kind === 'alpha') {
            return "Remaining: Alpha " + value.metadata;
        } else {
            // This should infer that value is { kind: 'delta', callback: (x: number) => boolean, priority: number }
            return "Remaining: Delta priority " + value.priority.toString();
        }
    }
}

function testChainedElimination(value: ChainedElimination): string {
    // Test multiple sequential eliminations
    if (value.kind === 'type1') {
        return "Type1: " + value.a.toString();
    } else {
        // Here value should be narrowed to exclude 'type1'
        if (value.kind === 'type2') {
            return "Type2: " + value.b;
        } else {
            // Here value should be narrowed to exclude 'type1' and 'type2'  
            if (value.kind === 'type3') {
                return "Type3: " + value.c.toString();
            } else {
                // Here value should be narrowed to exclude 'type1', 'type2', 'type3'
                if (value.kind === 'type4') {
                    return "Type4: " + value.d.length.toString() + " strings";
                } else {
                    // This should infer that value is { kind: 'type5', e: { x: number, y: number } }
                    let e = value.e;
                    return "Type5: (" + e.x.toString() + ", " + e.y.toString() + ")";
                }
            }
        }
    }
}

type GenericElimination<T> = 
    | { kind: 'success', result: T }
    | { kind: 'failure', error: string };

function testGenericElimination<T>(value: GenericElimination<T>): string {
    if (value.kind === 'success') {
        // value.result should be accessible as T
        return "Success with result";
    } else {
        // This should infer that value is { kind: 'failure', error: string }
        return "Failure: " + value.error;
    }
}

function testGenericEliminationString(value: GenericElimination<string>): string {
    if (value.kind === 'success') {
        return "String success: " + value.result;
    } else {
        // This should infer that value is { kind: 'failure', error: string }
        return "String failure: " + value.error;
    }
}

function testGenericEliminationNumber(value: GenericElimination<number>): string {
    if (value.kind === 'success') {
        return "Number success: " + value.result.toString();
    } else {
        // This should infer that value is { kind: 'failure', error: string }
        return "Number failure: " + value.error;
    }
}

///////////////////////////////////////////////////////////////////////////////
// Elimination Refinement Test Runners
///////////////////////////////////////////////////////////////////////////////

function testSimpleEliminationCases(): void {
    let valueA: SimpleADT = { kind: 'a' };
    let valueB: SimpleADT = { kind: 'b', msg: 'hello' };
    
    console.log(testSimpleElimination(valueA));
    console.log(testSimpleElimination(valueB));
}

function testThreeVariantEliminationCases(): void {
    let first: ThreeVariantADT = { kind: 'first', data: 42 };
    let second: ThreeVariantADT = { kind: 'second', info: 'test' };
    let third: ThreeVariantADT = { kind: 'third', flag: true };
    
    console.log(testThreeVariantElimination(first));
    console.log(testThreeVariantElimination(second));
    console.log(testThreeVariantElimination(third));
}

function deltaFn(n: number): string {
    return "Number: " + n.toString();
}

function deltaCallback(x: number): boolean {
    return x > 0;
}

function testComplexEliminationCases(): void {
    let alpha: ComplexElimination = { kind: 'alpha', x: 10, y: 'test' };
    
    let betaItems: Array<number> = new Array<number>();
    betaItems.push(1);
    betaItems.push(2);
    betaItems.push(3);
    let beta: ComplexElimination = { kind: 'beta', items: betaItems };
    
    let gamma: ComplexElimination = { kind: 'gamma', nested: { a: true, b: 100 } };
    
    let delta: ComplexElimination = { kind: 'delta', fn: deltaFn };
    
    console.log(testComplexElimination(alpha));
    console.log(testComplexElimination(beta));
    console.log(testComplexElimination(gamma));
    console.log(testComplexElimination(delta));
}

function testNestedEliminationCases(): void {
    let outer1: NestedElimination = { kind: 'outer', inner: { kind: 'inner1', val: 123 } };
    let outer2: NestedElimination = { kind: 'outer', inner: { kind: 'inner2', text: 'nested' } };
    let simple: NestedElimination = { kind: 'simple', value: false };
    
    console.log(testNestedElimination(outer1));
    console.log(testNestedElimination(outer2));
    console.log(testNestedElimination(simple));
}

function testFourBranchEliminationCases(): void {
    let alphaItems: Array<string> = new Array<string>();
    alphaItems.push("item1");
    alphaItems.push("item2");
    
    let alpha: FourBranchADT = { kind: 'alpha', value: 100, metadata: 'test metadata' };
    let beta: FourBranchADT = { kind: 'beta', items: alphaItems, count: 5 };
    let gamma: FourBranchADT = { kind: 'gamma', flag: true, config: { enabled: true, timeout: 1000 } };
    let delta: FourBranchADT = { kind: 'delta', callback: deltaCallback, priority: 3 };
    
    console.log("=== Four Branch Complete Elimination ===");
    console.log(testFourBranchElimination(alpha));
    console.log(testFourBranchElimination(beta));
    console.log(testFourBranchElimination(gamma));
    console.log(testFourBranchElimination(delta));
    
    console.log("=== Four Branch Partial Elimination ===");
    console.log(testFourBranchPartialElimination(alpha));
    console.log(testFourBranchPartialElimination(beta));
    console.log(testFourBranchPartialElimination(gamma));
    console.log(testFourBranchPartialElimination(delta));
    
    console.log("=== Four Branch Middle Elimination ===");
    console.log(testFourBranchMiddleElimination(alpha));
    console.log(testFourBranchMiddleElimination(beta));
    console.log(testFourBranchMiddleElimination(gamma));
    console.log(testFourBranchMiddleElimination(delta));
}

function testChainedEliminationCases(): void {
    let type1: ChainedElimination = { kind: 'type1', a: 1 };
    let type2: ChainedElimination = { kind: 'type2', b: 'two' };
    let type3: ChainedElimination = { kind: 'type3', c: true };
    
    let type4Items: Array<string> = new Array<string>();
    type4Items.push('item1');
    type4Items.push('item2');
    let type4: ChainedElimination = { kind: 'type4', d: type4Items };
    
    let type5: ChainedElimination = { kind: 'type5', e: { x: 5, y: 10 } };
    
    console.log(testChainedElimination(type1));
    console.log(testChainedElimination(type2));
    console.log(testChainedElimination(type3));
    console.log(testChainedElimination(type4));
    console.log(testChainedElimination(type5));
}

function testGenericEliminationCases(): void {
    let stringSuccess: GenericElimination<string> = { kind: 'success', result: 'test result' };
    let stringFailure: GenericElimination<string> = { kind: 'failure', error: 'string error' };
    
    let numberSuccess: GenericElimination<number> = { kind: 'success', result: 42 };
    let numberFailure: GenericElimination<number> = { kind: 'failure', error: 'number error' };
    
    console.log(testGenericEliminationString(stringSuccess));
    console.log(testGenericEliminationString(stringFailure));
    console.log(testGenericEliminationNumber(numberSuccess));
    console.log(testGenericEliminationNumber(numberFailure));
}

///////////////////////////////////////////////////////////////////////////////
// Main Test Runner
///////////////////////////////////////////////////////////////////////////////

function runAllADTTests(): void {
    console.log("=== Basic ADT Tests ===");
    testBasicADTs();
    
    console.log("=== Shape ADT Tests ===");
    testShapeADTs();
    
    console.log("=== Nested ADT Tests ===");
    testNestedADTs();
    
    console.log("=== API Result Tests ===");
    testApiResults();
    
    console.log("=== State Machine Tests ===");
    testStateMachine();
    
    console.log("=== Tree ADT Tests ===");
    testTreeADT();
    
    console.log("=== Option ADT Tests ===");
    testOptionADT();
    
    console.log("=== Complex Nested ADT Tests ===");
    testComplexNestedADT();
    
    console.log("=== Elimination Refinement Tests ===");
    testSimpleEliminationCases();
    testThreeVariantEliminationCases();
    testComplexEliminationCases();
    testNestedEliminationCases();
    testFourBranchEliminationCases();
    testChainedEliminationCases();
    testGenericEliminationCases();
    
    console.log("All ADT tests completed successfully!");
}