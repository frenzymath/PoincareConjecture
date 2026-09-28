import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold Topology ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b : ℝ}

theorem backwardLLength_eq_of_eqOn {γ η : ℝ → M} (hab : a ≤ b)
    (h : EqOn γ η (Icc a b)) : backwardLLength F T a b γ = backwardLLength F T a b η := by
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le hab]
  intro s hs
  have heq : γ =ᶠ[𝓝 s] η := Filter.mem_of_superset (Ioo_mem_nhds hs.1 hs.2)
    (fun t ht => h (Ioo_subset_Icc_self ht))
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  simp only [backwardLIntegrand, curveVelocity, hd, heq.eq_of_nhds]
  congr 2
  exact congrArg (fun x => (F.metric (T - s)).inner x
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η s 1) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η s 1))
    heq.eq_of_nhds

theorem IsMinimizingBackwardLPath.congr {γ η : BackwardTimePath F T a b}
    (hmin : IsMinimizingBackwardLPath F T a b γ)
    (h : EqOn γ.curve η.curve (Icc a b)) : IsMinimizingBackwardLPath F T a b η := by
  have hab := γ.ordered.le
  intro q hq0 hq1
  rw [← backwardLLength_eq_of_eqOn hab h]
  exact hmin q (hq0.trans (h ⟨le_rfl, hab⟩).symm)
    (hq1.trans (h ⟨hab, le_rfl⟩).symm)

end PoincareConjecture
