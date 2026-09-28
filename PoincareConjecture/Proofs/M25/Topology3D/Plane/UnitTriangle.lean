import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

def unitTriangle : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

theorem convex_unitTriangle : Convex ℝ unitTriangle :=
  ((convex_Ici (𝕜 := ℝ) 0).linear_preimage (LinearMap.fst ℝ ℝ ℝ)).inter
    (((convex_Ici (𝕜 := ℝ) 0).linear_preimage (LinearMap.snd ℝ ℝ ℝ)).inter
      ((convex_Iic (𝕜 := ℝ) 1).linear_preimage
        (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)))

theorem unitTriangle_eq_convexHull :
    unitTriangle = convexHull ℝ {(0, 0), (1, 0), (0, 1)} := by
  apply subset_antisymm
  · intro z hz
    change 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1 at hz
    refine mem_convexHull_of_exists_fintype
      ![1 - z.1 - z.2, z.1, z.2] ![(0, 0), (1, 0), (0, 1)] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · change 0 ≤ 1 - z.1 - z.2
        linarith [hz.2.2]
      · exact hz.1
      · exact hz.2.1
    · simp only [Fin.sum_univ_three]
      change 1 - z.1 - z.2 + z.1 + z.2 = 1
      ring
    · intro i
      fin_cases i <;> simp
    · simp only [Fin.sum_univ_three]
      ext <;> simp
  · apply convexHull_min _ convex_unitTriangle
    rintro z (rfl | rfl | rfl) <;> norm_num [unitTriangle]

theorem interior_unitTriangle :
    interior unitTriangle = {z | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1} := by
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ
  have hL : Continuous L := continuous_fst.add continuous_snd
  have hLo : IsOpenMap L := L.isOpenMap_of_finiteDimensional fun t => ⟨(t, 0), by simp [L]⟩
  have hF := IsOpenMap.preimage_interior_eq_interior_preimage
    (isOpenMap_fst : IsOpenMap (Prod.fst : ℝ × ℝ → ℝ)) continuous_fst (Ici 0)
  have hS := IsOpenMap.preimage_interior_eq_interior_preimage
    (isOpenMap_snd : IsOpenMap (Prod.snd : ℝ × ℝ → ℝ)) continuous_snd (Ici 0)
  have hT := hLo.preimage_interior_eq_interior_preimage hL (Iic 1)
  change interior ((Prod.fst ⁻¹' Ici 0) ∩ ((Prod.snd ⁻¹' Ici 0) ∩ (L ⁻¹' Iic 1))) = _
  rw [interior_inter, interior_inter, ← hF, ← hS, ← hT, interior_Ici, interior_Iic]
  rfl

theorem closure_interior_unitTriangle : closure (interior unitTriangle) = unitTriangle := by
  have hclosed : IsClosed unitTriangle :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hnonempty : (interior unitTriangle).Nonempty := by
    rw [interior_unitTriangle]
    exact ⟨(1 / 3, 1 / 3), by norm_num⟩
  rw [convex_unitTriangle.closure_interior_eq_closure_of_nonempty_interior hnonempty,
    hclosed.closure_eq]

end PoincareConjecture.M25.Topology3D
