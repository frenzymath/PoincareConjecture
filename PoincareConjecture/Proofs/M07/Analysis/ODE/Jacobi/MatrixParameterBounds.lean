

import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.ParameterBounds

open Set
open scoped ContDiff
noncomputable section

namespace Poincare.ODE.Jacobi

universe u
variable {P F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance : NormedAddCommGroup (F →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

theorem norm_iteratedFDeriv_matrixJacobi_le
    (n : ℕ) {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {U : Set P} (hU : IsOpen U) {W : Set (ℝ × P)} (hW : IsOpen W)
    (hUW : Icc a b ×ˢ U ⊆ W)
    {R J V : ℝ × P → F →L[ℝ] F}
    (hR : ContDiffOn ℝ ∞ R W) (hJ : ContDiffOn ℝ ∞ J W)
    (hV : ContDiffOn ℝ ∞ V W)
    (hJode : ∀ z ∈ W, Poincare.ODE.Parameter.timeFDeriv J z = V z)
    (hVode : ∀ z ∈ W, Poincare.ODE.Parameter.timeFDeriv V z = -(R z).comp (J z))
    (hJinit : ∀ p ∈ U, J (a, p) = 0)
    (hVinit : ∀ p ∈ U, V (a, p) = ContinuousLinearMap.id ℝ F)
    (hbound : ∀ j ≤ n, ∀ t ∈ Icc a b, ∀ p ∈ U,
      ‖iteratedFDeriv ℝ j (fun q => R (t, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q => (J (t, q), V (t, q))) p‖ ≤
      Real.exp ((2 : ℝ) ^ n * max 1 C * (t - a)) := by
  let L := ContinuousLinearMap.compL ℝ F F F
  have hLR : ContDiffOn ℝ ∞ (fun z => L (R z)) W := L.contDiff.comp_contDiffOn hR
  have hLbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun x => L (R (s, x))) q‖ ≤ C := by
    intro j hj s hs q hq
    have hRq : ContDiffAt ℝ ∞ (fun x => R (s, x)) q :=
      ((hR _ (hUW ⟨hs, hq⟩)).contDiffAt (hW.mem_nhds (hUW ⟨hs, hq⟩))).comp q
        (contDiffAt_const.prodMk contDiffAt_id)
    have h := L.norm_iteratedFDeriv_comp_left hRq
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    have hb := mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ F F F)
      (norm_nonneg (iteratedFDeriv ℝ j (fun x => R (s, x)) q))
    rw [one_mul] at hb
    exact (h.trans hb).trans (hbound j hj s hs q hq)
  have h := norm_iteratedFDeriv_jacobi_le n hab hC hU hW hUW hLR hJ hV hJode
    hVode hJinit hVinit hLbound ht hp
  refine h.trans ?_
  have hinit : max ‖(0 : F →L[ℝ] F)‖ ‖ContinuousLinearMap.id ℝ F‖ ≤ 1 :=
    max_le (by simp) (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hinit
    (Real.exp_nonneg ((2 : ℝ) ^ n * max 1 C * (t - a)))

end Poincare.ODE.Jacobi
