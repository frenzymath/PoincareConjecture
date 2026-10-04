import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FixedRadialNormalization
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.PlanarCycleConfigurationSpace

/-!
# Contractibility of radial cycles with a fixed edge

The two marked unit vertices remain fixed during radial normalization.
Consequently the full radial realization space with that frame is
contractible, without unit-norm restrictions on its other vertices.
See Cairns 1940, Lemma 5.3, pp. 801--802, and p. 807, footnote 14;
M76 derivation 24.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Smoothing

/-- Prescribed values for the two marked vertices. Values outside
labels zero and one do not constrain the realization.
See Cairns p. 801 and M76 derivation 24. -/
noncomputable def cycleFrame (n : ℕ) (theta : ℝ) (i : Fin (n + 3)) : ℂ :=
  if i = 0 then 1 else Circle.exp theta

/-- The fixed-frame equations prescribe exactly the two adjacent
vertices. See Cairns p. 801 and M76 derivation 24. -/
theorem fixedCycleVertexValues_iff {n : ℕ} {theta : ℝ}
    (v : (cyclicEdgeComplex n).RadialEmbedding ℂ) :
    EqOn v.val (cycleFrame n theta) ({0, 1} : Set (Fin (n + 3))) ↔
      v.val 0 = 1 ∧ v.val 1 = (Circle.exp theta : ℂ) := by
  have hne : (1 : Fin (n + 3)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one, Fin.val_zero] at hv
    omega
  constructor
  · intro h
    exact ⟨by simpa [cycleFrame] using h (by simp : (0 : Fin (n + 3)) ∈
      ({0, 1} : Set (Fin (n + 3)))),
      by simpa only [cycleFrame, if_neg hne] using h (by simp : (1 : Fin (n + 3)) ∈
        ({0, 1} : Set (Fin (n + 3))))⟩
  · rintro ⟨hzero, hone⟩ i (rfl | hi)
    · simpa [cycleFrame] using hzero
    · rw [mem_singleton_iff] at hi
      subst i
      simpa only [cycleFrame, if_neg hne] using hone

/-- Faithful radial cycle realizations with the first two vertices
fixed as a coordinate frame. Other vertices may have arbitrary positive
radii. See Cairns pp. 801--802 and M76 derivation 24. -/
abbrev FixedEdgeCycleSpace (n : ℕ) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedRadialEmbedding ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

/-- The constrained unit subspace is exactly the normalized unit cycle
space previously described in angular coordinates.
See Cairns pp. 801--802 and M76 derivation 24. -/
noncomputable def fixedUnitCycleHomeomorph (n : ℕ) (theta : ℝ) :
    (cyclicEdgeComplex n).FixedUnitRadialEmbedding ({0, 1} : Set (Fin (n + 3)))
      (cycleFrame n theta) ≃ₜ normalizedUnitCycleSpace n theta := by
  apply Homeomorph.setCongr
  ext v
  change EqOn v.val.val (cycleFrame n theta) ({0, 1} : Set (Fin (n + 3))) ↔
    unitCycleVertex v 0 = 1 ∧ unitCycleVertex v 1 = Circle.exp theta
  rw [fixedCycleVertexValues_iff]
  constructor
  · rintro ⟨hzero, hone⟩
    exact ⟨Circle.ext hzero, Circle.ext hone⟩
  · rintro ⟨hzero, hone⟩
    exact ⟨congrArg (fun z : Circle => (z : ℂ)) hzero,
      congrArg (fun z : Circle => (z : ℂ)) hone⟩

/-- Fixing an independent unit edge makes the full radial cycle
realization space contractible in vertex topology. Unit norms on other
vertices are not assumed. See Cairns pp. 801--802, 807 and
M76 derivation 24. -/
theorem contractible_fixedEdgeCycleSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) : ContractibleSpace (FixedEdgeCycleSpace n theta) := by
  apply (AbstractSimplicialComplex.contractible_fixedRadialEmbedding_iff
    (cyclicEdgeComplex n) ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta) ?_).mpr
  · let := contractible_normalizedUnitCycleSpace n htheta
    exact (fixedUnitCycleHomeomorph n theta).contractibleSpace
  · intro i _
    dsimp only [cycleFrame]
    split_ifs
    · exact norm_one
    · exact Circle.norm_coe _

end PoincareMT.M76.Smoothing
