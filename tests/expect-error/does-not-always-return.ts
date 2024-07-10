
// @ts-expect-error This function may not always return a value
function doesNotAlwaysReturnAValue(b: boolean): boolean {
    switch (b) {
        case true:
            return true;
    }
}
