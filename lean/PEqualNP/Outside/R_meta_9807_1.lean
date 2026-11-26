import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9807_1
  (caseAnd :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 24 →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = (fun x : Fin 14 → Bool => (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)) x) →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output - 14]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      False)
  (caseOther :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 24 →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = (fun x : Fin 14 → Bool => (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)) x) →
      (¬ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output - 14]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      False) :
    ¬ (PEqualNP.MetaComplexity.HasCircuitSize 14 (fun x : Fin 14 → Bool => (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)) 24) := by
  classical
  intro h
  obtain ⟨C, hfan, hsize, heval⟩ := h
  by_cases hq : ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output - 14]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact caseAnd C hfan hsize heval hq
  · exact caseOther C hfan hsize heval hq
