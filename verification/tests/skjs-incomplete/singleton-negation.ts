/**
 * Incompleteness witness: negating flag : true always produces false, but SKJS
 * exports boolean and rejects the annotation. Repair only the
 * negation-expression claim to false; the verifier checks it using the
 * known-condition rule.
 */
function negateSingleton(flag: true): false {
  return !flag;
}
