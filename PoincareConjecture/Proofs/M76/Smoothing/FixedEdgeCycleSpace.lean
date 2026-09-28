import PoincareConjecture.Proofs.M76.Mathlib.FixedRadialNormalization
import PoincareConjecture.Proofs.M76.Smoothing.PlanarCycleConfigurationSpace

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Smoothing

noncomputable def cycleFrame (n : ℕ) (theta : ℝ) (i : Fin (n + 3)) : ℂ :=
  if i = 0 then 1 else Circle.exp theta

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

abbrev FixedEdgeCycleSpace (n : ℕ) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedRadialEmbedding ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

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

end PoincareConjecture.M76.Smoothing
