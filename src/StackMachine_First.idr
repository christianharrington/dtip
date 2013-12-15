module StackMachine_First

-- Consumed, produced
data Inst : Nat -> Nat -> Type where
  PUSH  : Int -> Inst c p -> Inst c (1 + p)
  ADD   : Inst c (2 + p) -> Inst c (1 + p)
  SUB   : Inst c (2 + p) -> Inst c (1 + p)
  START : Inst 0 0

test : Inst 0 1
test = ADD (PUSH 2 (PUSH 1 START))

run : Inst 0 p -> Vect p Int
run START      = []
run (PUSH v i) =  v :: run i
run (ADD i)    = case (run i) of
                      v1 :: v2 :: vs => (v1 + v2) :: vs
run (SUB i)    = case (run i) of
                      v1 :: v2 :: vs => (v1 - v2) :: vs
