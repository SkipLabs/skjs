
// @ts-expect-error
function doesNotAlwaysReturnAValue(b: boolean): boolean {
    switch (b) {
        case true:
            return true;
    }
}
