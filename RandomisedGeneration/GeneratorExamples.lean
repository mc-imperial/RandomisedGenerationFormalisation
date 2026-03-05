import RandomisedGeneration.Generator

namespace RandomisedGeneration

namespace GeneratorExamples

def simpleGenerator : Generator (Fin 1) (Fin 2) (Fin 1) where
  init  := 0
  blank := 0
  δ := fun _q b _w =>
    if b then
      some (0, 0, some 1, InputTapeDirection.R, WorkTapeDirection.N)
    else
      none

-- On all-zeros bitstream: halts immediately with no output
example : Computes simpleGenerator (initConfig simpleGenerator (fun _ => false)) [] := by
  apply Computes.halt
  simp [step, simpleGenerator, initConfig]

-- On bitstream 1,1,0,...: outputs [1, 1] then halts
example : Computes simpleGenerator
    (initConfig simpleGenerator (fun n => n < 2)) [1, 1] := by
  apply Computes.step _ _ _ (by simp only [step, simpleGenerator, initConfig]; rfl)
  apply Computes.step _ _ _ (by simp only [step, simpleGenerator]; rfl)
  apply Computes.halt
  simp [step, simpleGenerator]

-- On bitstream 1,0,...: outputs [1] then halts
example : Computes simpleGenerator
    (initConfig simpleGenerator (fun n => n = 0)) [1] := by
  apply Computes.step _ _ _ (by simp only [step, simpleGenerator, initConfig]; rfl)
  apply Computes.halt
  simp [step, simpleGenerator]

-- Work tape alphabet: Fin 2
--   0 = blank
--   1 = tally mark
-- Output alphabet: Fin 2 (output 1s, ignore 0s)
-- States: Fin 3
--   0 = scanning input rightward, writing tally marks on work tape
--   1 = scanning work tape leftward back to origin
--   2 = scanning work tape rightward, outputting one 1 per mark
def tallyGenerator : Generator (Fin 2) (Fin 2) (Fin 3) where
  init  := 0
  blank := 0
  δ := fun q b w =>
    match q, b, w with
    -- State 0: scanning input
    -- bit=1: write mark on work tape, move work right, advance input
    | 0, true,  _ => some (0, 1, none, InputTapeDirection.R, WorkTapeDirection.R)
    -- bit=0: stop reading; move work tape left, go to state 1
    | 0, false, _ => some (1, w, none, InputTapeDirection.N, WorkTapeDirection.L)
    -- State 1: scanning left to find start (blank cell)
    -- still on a mark: keep going left
    | 1, _, 1 => some (1, 1, none,     InputTapeDirection.N, WorkTapeDirection.L)
    -- hit a blank: we're at the start, switch to rightward output scan
    | 1, _, 0 => some (2, 0, none,     InputTapeDirection.N, WorkTapeDirection.R)
    -- State 2: scanning right, outputting
    -- mark found: output a 1, clear the mark, move right
    | 2, _, 1 => some (2, 0, some 1,   InputTapeDirection.N, WorkTapeDirection.R)
    -- blank found: done
    | 2, _, 0 => none
    | _, _, _ => none

def moveRightGenerator : Generator (Fin 10) (Fin 10) (Fin 10) where
  init  := 0
  blank := 0
  δ := fun q b w =>
    match q, b, w with
    | 0, _,  _ => some (1, 0, some 0, InputTapeDirection.R, WorkTapeDirection.R)
    | 1, _,  _ => some (2, 1, some 1, InputTapeDirection.R, WorkTapeDirection.R)
    | 2, _,  _ => some (3, 2, some 2, InputTapeDirection.R, WorkTapeDirection.R)
    | 3, _,  _ => some (4, 3, some 3, InputTapeDirection.R, WorkTapeDirection.R)
    | 4, _,  _ => some (5, 4, some 4, InputTapeDirection.R, WorkTapeDirection.R)
    | 5, _,  _ => some (6, 5, some 5, InputTapeDirection.R, WorkTapeDirection.R)
    | 6, _,  _ => some (7, 6, some 6, InputTapeDirection.R, WorkTapeDirection.R)
    | 7, _,  _ => some (8, 7, some 7, InputTapeDirection.R, WorkTapeDirection.R)
    | 8, _,  _ => some (9, 8, some 8, InputTapeDirection.R, WorkTapeDirection.R)
    | 9, _,  _ => none

def moveLeftGenerator : Generator (Fin 10) (Fin 10) (Fin 10) where
  init  := 0
  blank := 0
  δ := fun q b w =>
    match q, b, w with
    | 0, _,  _ => some (1, 0, some 0, InputTapeDirection.R, WorkTapeDirection.L)
    | 1, _,  _ => some (2, 1, some 1, InputTapeDirection.R, WorkTapeDirection.L)
    | 2, _,  _ => some (3, 2, some 2, InputTapeDirection.R, WorkTapeDirection.L)
    | 3, _,  _ => some (4, 3, some 3, InputTapeDirection.R, WorkTapeDirection.L)
    | 4, _,  _ => some (5, 4, some 4, InputTapeDirection.R, WorkTapeDirection.L)
    | 5, _,  _ => some (6, 5, some 5, InputTapeDirection.R, WorkTapeDirection.L)
    | 6, _,  _ => some (7, 6, some 6, InputTapeDirection.R, WorkTapeDirection.L)
    | 7, _,  _ => some (8, 7, some 7, InputTapeDirection.R, WorkTapeDirection.L)
    | 8, _,  _ => some (9, 8, some 8, InputTapeDirection.R, WorkTapeDirection.L)
    | 9, _,  _ => none

end GeneratorExamples

end RandomisedGeneration
