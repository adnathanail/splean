import Mathlib.Tactic.TypeStar

/-- Extract the value from an Except, panicking on error -/
def Except.get! {α ε : Type*} [Inhabited α] : Except ε α → α
  | .ok a => a
  | .error _ => panic! "Except.get! called on .error"

/-- Check if an Except is an error -/
def Except.isError {ε α : Type*} : Except ε α → Bool
  | .ok _ => false
  | .error _ => true

/-- Convert an Option to Except, using the given error message for `none` -/
def Option.toExcept {α : Type*} (msg : String) : Option α → Except String α
  | some a => .ok a
  | none => .error msg

/-- Insert an element into a sorted list (structural recursion, kernel-reducible).
    Distinct from Mathlib's `List.orderedInsert`, which takes a relation;
    this version uses an `[Ord α]` instance via `compare`. -/
def List.orderedInsertByOrd {α : Type*} [Ord α] (a : α) : List α → List α
  | [] => [a]
  | b :: l => if (compare a b).isLE then a :: b :: l else b :: List.orderedInsertByOrd a l

/-- Insertion sort using structural recursion (kernel-reducible, unlike mergeSort).
    Distinct from Mathlib's `List.insertionSort`, which takes a relation;
    this version uses an `[Ord α]` instance via `compare`. -/
def List.insertionSortByOrd {α : Type*} [Ord α] : List α → List α
  | [] => []
  | a :: l => (List.insertionSortByOrd l).orderedInsertByOrd a
