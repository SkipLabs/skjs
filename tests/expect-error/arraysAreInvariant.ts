
///////////////////////////////////////////////////////////////////////////////
// Intersection of Top
///////////////////////////////////////////////////////////////////////////////

// This currently gives Array<Top>
type arrayNumberOrArrayString = Array<number> | Array<string>;

// Involves an inst which is both an intersection and a named type
// while destructing the array type
function interWithTop<T>(...x: T[] & arrayNumberOrArrayString): T {
    return x[0];
}

function checkIntersectionWithTopIsNotBottom(): number {
    // @ts-expect-error Invalid call. Unexpected type for ...
    return interWithTop(0) + 1; // ensure the result is a (subtype of a) number
}
