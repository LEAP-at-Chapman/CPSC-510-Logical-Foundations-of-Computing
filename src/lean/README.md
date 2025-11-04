# Dependent Types vs Regular Types: Matrix Column Averaging

This directory contrasts Haskell's standard type system with Lean 4's dependent types through a concrete example: averaging a matrix column.

## The Problem

Given a matrix, extract a column and compute its average. Simple? Not quite. Two key issues arise:

1. **Out-of-bounds access**: What if we request column index 5 from a 3-column matrix?
2. **Division by zero**: What if the matrix is empty (no rows)?

## Haskell Version (`averageColumn.hs`)

Haskell uses **regular types** - types cannot depend on runtime values like sizes or indices.

```haskell
type Matrix a = [[a]]

getColumn :: Int -> Matrix a -> [a]
getColumn n = map (!! n)  -- Unsafe: no bounds checking!

averageColumn :: Int -> Matrix Double -> Double
averageColumn n mat =
    let col = getColumn n mat
        len = length col
    in sum col / fromIntegral len  -- Unsafe: could divide by zero!
```

Run in the terminal with `runhaskell averageColumn.hs`

**Example runtime failures:**
```haskell
averageColumn 5 matrix1     -- CRASH: index out of bounds
averageColumn 0 []          -- CRASH: division by zero
```

## Lean Version (`averageColumn.lean`)

Lean uses **dependent types** - types can depend on runtime values.

### Key Design Choices

**1. Size-indexed vectors**
```lean
inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
```
The type `Vect α n` encodes the length `n` in the type itself.

**2. Bounded indices**
```lean
def getColumn {m n : Nat} (mat : Matrix α m n) (col : Fin n) : Vect α m
```
- Matrix dimensions `m × n` are part of the type
- Column index has type `Fin n` (bounded numbers: 0..n-1)

**3. Proof requirements**
```lean
def averageColumn (mat : Matrix α m n) (col : Fin n) (_ : m > 0) : α
```
The type requires a proof `m > 0` that the matrix is non-empty.

**Benefits:**
- Invalid column indices are rejected at **compile time**
- Division by zero is prevented by requiring a proof
- Type system enforces matrix dimensions are consistent
- If it compiles, certain runtime errors cannot occur

**Example:**
```lean
def validColumn : Fin 3 := ⟨1, by decide⟩
#eval averageColumn matrix1 validColumn (by decide : 2 > 0)  -- Works: 3.5

-- This won't compile - can't create a Fin 3 with value 5
-- def invalidColumn : Fin 3 := ⟨5, by decide⟩  -- Type error!
```

Run in the terminal with `lean averageColumn.lean` 

## Tradeoffs

### Haskell
- ✅ Simple, familiar type system
- ✅ Fast compilation
- ✅ Flexible for rapid prototyping
- ❌ Runtime crashes from type-unsafe operations
- ❌ Must rely on testing to catch errors

### Lean
- ✅ Catch certain classes of bugs at compile time
- ✅ Eliminate entire categories of runtime errors
- ✅ Types encode more information about program properties
- ❌ More complex type system
- ❌ More verbose code
- ❌ Slower compilation
- ❌ More difficult to learn

