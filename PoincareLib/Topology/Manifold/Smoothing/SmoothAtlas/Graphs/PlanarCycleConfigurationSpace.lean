import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.PlanarCycleCoordinates

/-!
# Contractibility of normalized planar cycle realizations

Fixing the first two unit vertices identifies the full radial cycle
realization space with the convex short-gap space. Both maps are
continuous in the actual vertex topology. No angular-order premise is
assumed on the realization side. This is the planar configuration-space
calculation of Cairns 1940, pp. 802, 807; see M76 derivation 23.
-/

set_option autoImplicit false

open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- Unit radial cycle realizations with only the two marked adjacent
vertices prescribed. See Cairns pp. 801--802 and M76 derivation 23. -/
def normalizedUnitCycleSpace (n : ℕ) (theta : ℝ) :
    Set ((cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  {v | unitCycleVertex v 0 = 1 ∧ unitCycleVertex v 1 = Circle.exp theta}

/-- The circle vertex of the constructed polygon is its prescribed
exponential. See Cairns p. 802 and M76 derivation 23. -/
theorem unitCycleVertex_planarGapEmbedding (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    unitCycleVertex (planarGapEmbedding w) i = Circle.exp (gapAngle w i) := rfl

/-- The polygon constructed from gaps satisfies the two marked-vertex
constraints. See Cairns p. 802 and M76 derivation 23. -/
noncomputable def normalizedGapEmbedding (w : shortArcGapSpace n theta) :
    normalizedUnitCycleSpace n theta :=
  ⟨planarGapEmbedding w, by
    constructor
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_zero, Circle.exp_zero]
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_one w.property]⟩

/-- Recovering increments from a constructed polygon returns its
original gaps, including the closing gap.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- Unit circle vertices depend continuously on radial vertex
coordinates. See Cairns p. 801 and M76 derivation 23. -/
theorem continuous_unitCycleVertex (i : Fin (n + 3)) :
    Continuous (fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ => unitCycleVertex v i) :=
  ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

/-- The short-increment tuple is continuous on the entire unit radial
cycle space: independent edges exclude the argument cut.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- The full normalized unit radial cycle space is homeomorphic to its
short-gap coordinates. Geometric incidence forces the positive cyclic
order in the inverse construction. See Cairns pp. 802, 807 and
M76 derivation 23. -/
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

/-- Normalized planar cycle realizations are contractible in the
subspace topology of their vertex positions.
See Cairns p. 807, footnote 14 and M76 derivation 23. -/
theorem contractible_normalizedUnitCycleSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (normalizedUnitCycleSpace n theta) := by
  let := contractible_shortArcGapSpace n htheta
  exact (gapUnitCycleHomeomorph n htheta).symm.contractibleSpace

end PoincareMT.M76.Smoothing
