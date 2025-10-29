-- Vect is like the predefined Vector
inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

def sumVect [Add α] [OfNat α 0] : Vect α n → α
  | .nil => 0
  | .cons x xs => x + sumVect xs

structure Matrix (α : Type) (m n : Nat) where
  data : Vect (Vect α n) m
  -- Vect (Vect α n) m is like the predefined Matrix α m n

-- Get column from matrix (simplified implementation)
def getColumn {α : Type} {m n : Nat} (mat : Matrix α m n) (col : Fin n) : Vect α m :=
  let rec extractCol : (m' : Nat) → Vect (Vect α n) m' → Vect α m'
    | 0, .nil => .nil
    | _+1, .cons row rows =>
        let elem := getElem _ row col
        .cons elem (extractCol _ rows)
  extractCol m mat.data
  where
  getElem : (n' : Nat) → Vect α n' → Fin n' → α
    | _+1, .cons x _, ⟨0, _⟩ => x
    | _+1, .cons _ xs, ⟨i+1, h⟩ => getElem _ xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

-- Average of a column - requires proof that matrix is non-empty
def averageColumn {α : Type} [HDiv α Float α] [Add α] [OfNat α 0] {n m : Nat} (mat : Matrix α m n) (col : Fin n) (_ : m > 0) : α :=
  let column := getColumn mat col
  let sum := sumVect column
  sum / (m.toFloat : Float)

-- Example: 2x3 matrix
def matrix1 : Matrix Float 2 3 :=
  let row1 := Vect.cons 1.0 (.cons 2.0 (.cons 3.0 .nil))
  let row2 := Vect.cons 4.0 (.cons 5.0 (.cons 6.0 .nil))
  ⟨Vect.cons row1 (.cons row2 .nil)⟩

-- This works: averages column 1 of matrix1
def validColumn : Fin 3 := ⟨1, by decide⟩
#eval averageColumn matrix1 validColumn (by decide : 2 > 0)  -- Should print 3.5

-- This won't compile - can't create a Fin 3 with value 5
def invalidColumn : Fin 3 := ⟨5, by decide⟩  -- Error: 5 < 3 = false

-- This won't compile - can't prove 0 > 0
def emptyMatrix : Matrix Float 0 3 := ⟨Vect.nil⟩
#eval averageColumn emptyMatrix validColumn (by decide : 0 > 0)  -- Error!
