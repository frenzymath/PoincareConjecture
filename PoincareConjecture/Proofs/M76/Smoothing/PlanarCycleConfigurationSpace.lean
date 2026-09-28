import PoincareConjecture.Proofs.M76.Smoothing.PlanarCycleCoordinates











set_option autoImplicit false

open Set NormedSpace

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ} {theta : ℝ}



def normalizedUnitCycleSpace (n : ℕ) (theta : ℝ) :
    Set ((cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  {v | unitCycleVertex v 0 = 1 ∧ unitCycleVertex v 1 = Circle.exp theta}



theorem unitCycleVertex_planarGapEmbedding (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    unitCycleVertex (planarGapEmbedding w) i = Circle.exp (gapAngle w i) := rfl



noncomputable def normalizedGapEmbedding (w : shortArcGapSpace n theta) :
    normalizedUnitCycleSpace n theta :=
  ⟨planarGapEmbedding w, by
    constructor
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_zero, Circle.exp_zero]
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_one w.property]⟩




theorem cycleIncrement_planarGapEmbedding (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    cycleIncrement (planarGapEmbedding w) i = w.val i := by
  have hend : unitCycleVertex (planarGapEmbedding w) (i + 1) =
      unitCycleVertex (planarGapEmbedding w) i * Circle.exp (w.val i) := by
    rw [unitCycleVertex_planarGapEmbedding, unitCycleVertex_planarGapEmbedding,
      ← Circle.exp_add]
    apply Circle.ext
    exact (planarGapVertices_endpoint w i).symm
  unfold cycleIncrement Circle.shortIncrement
  rw [hend, mul_div_cancel_left]
  exact Circle.arg_exp (by linarith [Real.pi_pos, (w.property.1 i).1]) (w.property.1 i).2.le



theorem continuous_unitCycleVertex (i : Fin (n + 3)) :
    Continuous (fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ => unitCycleVertex v i) :=
  ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _




theorem continuous_cycleIncrement :
    Continuous (cycleIncrement : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ →
      Fin (n + 3) → ℝ) := by
  apply continuous_pi
  intro i
  have hc : Continuous (fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ =>
      ((unitCycleVertex v (i + 1) / unitCycleVertex v i : Circle) : ℂ)) :=
    continuous_subtype_val.comp
      ((continuous_unitCycleVertex (i + 1)).div' (continuous_unitCycleVertex i))
  apply continuous_iff_continuousAt.mpr
  intro v
  have hs : ((unitCycleVertex v (i + 1) / unitCycleVertex v i : Circle) : ℂ) ∈
      Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.mpr
      ⟨(cycleIncrement_mem_Ioo v i).2.ne, Circle.coe_ne_zero _⟩
  exact (Complex.continuousAt_arg hs).comp
    (f := fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ =>
      ((unitCycleVertex v (i + 1) / unitCycleVertex v i : Circle) : ℂ)) hc.continuousAt





noncomputable def gapUnitCycleHomeomorph (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    shortArcGapSpace n theta ≃ₜ normalizedUnitCycleSpace n theta where
  toFun := normalizedGapEmbedding
  invFun v := ⟨cycleIncrement v.val,
    cycleIncrement_mem_shortArcGapSpace v.val htheta v.property.1 v.property.2⟩
  left_inv w := Subtype.ext (funext (cycleIncrement_planarGapEmbedding w))
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact planarGapVertices_cycleIncrement v.val htheta v.property.1 v.property.2
  continuous_toFun := continuous_planarGapEmbedding.subtype_mk _
  continuous_invFun := (continuous_cycleIncrement.comp continuous_subtype_val).subtype_mk _




theorem contractible_normalizedUnitCycleSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (normalizedUnitCycleSpace n theta) := by
  let := contractible_shortArcGapSpace n htheta
  exact (gapUnitCycleHomeomorph n htheta).symm.contractibleSpace

end PoincareConjecture.M76.Smoothing
