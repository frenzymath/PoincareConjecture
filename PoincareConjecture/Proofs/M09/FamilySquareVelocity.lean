import PoincareConjecture.Proofs.M09.FamilySlices
import PoincareConjecture.Proofs.M09.VelocityChainRules








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_square_velocity_eq (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (s : ℝ) (hs : s ∈ Set.Ioo 0 (Real.sqrt τmax)) :
    (curveVelocity (n := n) (A.squareFamily Z) s : EuclideanSpace ℝ (Fin n)) =
      (2 * s) • curveVelocity (n := n) (A.gamma Z) (s ^ 2) := by
  have hmaxpos : 0 < τmax := Real.sqrt_pos.mp (hs.1.trans hs.2)
  have hsmax : s ^ 2 < τmax := by
    nlinarith [hs.1, hs.2, Real.sq_sqrt hmaxpos.le]
  have hdiff := (lExponentialFamily_gammaSlice_contMDiffAt A Z (s ^ 2)
    (sq_pos_of_pos hs.1) hsmax).mdifferentiableAt (by simp)
  have heq : A.squareFamily Z =ᶠ[nhds s] fun r ↦ A.gamma Z (r ^ 2) := by
    apply Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
    intro r hr
    exact A.square_agrees Z r ⟨hr.1.le, hr.2⟩
  exact (curveVelocity_congr_of_eventuallyEq heq).trans
    (curveVelocity_comp_square (A.gamma Z) s hdiff)

end PoincareConjecture.Proofs.M09
