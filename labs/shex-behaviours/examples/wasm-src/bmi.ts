// Scalar ABI example: numbers in, number out. Any language that compiles to wasm will do;
// AssemblyScript is used here only so that the example builds without another toolchain.
export function bmi(massKg: f64, heightM: f64): f64 {
  return massKg / (heightM * heightM);
}
