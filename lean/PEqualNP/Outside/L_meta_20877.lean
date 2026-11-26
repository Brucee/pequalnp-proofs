import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20877_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32249889 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20877_aux

theorem PEqualNP.Outside.L_meta_20877 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32249889 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20877_aux.main
