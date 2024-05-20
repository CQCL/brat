# Brat Hugr Extension

The Brat Hugr Extension provides operations needed to represent Brat programs.

## Substitution Operations

| Name | Type Arguments | Inputs | Outputs | Meaning |
| ---- | -------------- | ------ | --------| ------- |
| `Hole` | `n: BoundedNat` <br> `Ss: List<Type>` <br> `Ts: List<Type>` | `*Ss`| `*Ts` | A hole indexed by `n`, to be filled in by a substitution |
| `Substitute` | `n: BoundedNat` <br> `FuncSig: Tuple<List<Type>, List<Type>>` <br> `HoleSigs: List<Tuple<List<Type>, List<Type>>>` | `FuncSig, *HoleSigs`| `*FuncSig` | Subsitutes the first `len(HoleSigs)` holes in the function plugged in as the first input. |


## Constructor Operations

In the following, we use `int` as a shorthand for the Hugr `arithmetic.int.types.int<6>` type and `List<T>` as a shorthand for `collections.List<T>`.

| Name | Type Arguments | Inputs | Outputs | Meaning |
| ---- | -------------- | ------ | --------| ------- |
| `Ctor::Nat::zero` | | | `int` | The `zero` constructor for natural numbers |
| `Ctor::Nat::succ` | | `int` | `int` | The `succ` constructor for natural numbers |
| `Ctor::Vec::nil` | `T: Type` | | `List<T>` | The `nil` constructor for vectors |
| `Ctor::Vec::cons` | `T: Type` | `T, List<T>` | `List<T>` | The `succ` constructor for vectors |


## Constructor Test Operations

In the following, we use `int` as a shorthand for the Hugr `arithmetic.int.types.int<6>` type and `List<T>` as a shorthand for `collections.List<T>`.

| Name | Type Arguments | Inputs | Outputs | Meaning |
| ---- | -------------- | ------ | --------| ------- |
| `PrimCtorTest::Nat::zero` | | `int` | `Sum((int), ())` | The test for the `zero` constructor for natural numbers |
| `PrimCtorTest::Nat::succ` | | `int` | `Sum((int), (int))` | The test for the `succ` constructor for natural numbers |
| `PrimCtorTest::Vec::nil` | `T: Type` | `List<T>` | `Sum((List<T>), ())` | The test for the `nil` constructor for vectors |
| `PrimCtorTest::Vec::cons` | `T: Type` | `List<T>` | `Sum((List<T>), (T, List<T>))` | The test for the `cons` constructor for vectors |


## Other Operations

| Name | Type Arguments | Inputs | Outputs | Meaning |
| ---- | -------------- | ------ | --------| ------- |
| `Panic` | `Ss: List<Type>` <br> `Ts: List<Type>` | `*Ss`| `*Ts` | A panic op with parametrised signature |
