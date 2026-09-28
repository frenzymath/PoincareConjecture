import PoincareConjecture.Proofs.M08.ClosedChartCoefficients
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M08

section MixedDerivative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def timeWithinFDeriv (C : Set ℝ) (U : Set E) (f : ℝ × E → H)
    (z : ℝ × E) : H := fderivWithin ℝ f (C ×ˢ U) z (1, 0)

theorem timeWithinFDeriv_contDiffOn {C : Set ℝ} {U : Set E}
    (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (f : ℝ × E → H)
    (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) :
    ContDiffOn ℝ ∞ (timeWithinFDeriv C U f) (C ×ˢ U) :=
  (hf.fderivWithin (hC.prod hU.uniqueDiffOn) (by simp)).clm_apply contDiffOn_const

theorem hasDerivWithinAt_timeWithin {C : Set ℝ} {U : Set E}
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    {s : ℝ} {x : E} (hs : s ∈ C) (hx : x ∈ U) :
    HasDerivWithinAt (fun r ↦ f (r, x)) (timeWithinFDeriv C U f (s, x)) C s := by
  have hd := ((hf (s, x) ⟨hs, hx⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hi : HasDerivWithinAt (fun r : ℝ ↦ (r, x)) (1, 0) C s :=
    (hasDerivWithinAt_id s C).prodMk (hasDerivWithinAt_const s C x)
  have hm : MapsTo (fun r : ℝ ↦ (r, x)) C (C ×ˢ U) := fun r hr ↦ ⟨hr, hx⟩
  exact hd.comp_hasDerivWithinAt s hi hm

theorem closed_time_spatial_commute {C : Set ℝ} {U : Set E}
    (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (f : ℝ × E → H)
    (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) {z : ℝ × E} (hz : z ∈ C ×ˢ U)
    (hzcl : z ∈ closure (interior (C ×ˢ U))) (v : E) :
    timeWithinFDeriv C U (spatialWithinFDeriv C U f) z v =
      spatialWithinFDeriv C U (timeWithinFDeriv C U f) z v := by
  let Ω := C ×ˢ U
  have hΩ : UniqueDiffOn ℝ Ω := hC.prod hU.uniqueDiffOn
  have hD := (((hf.fderivWithin hΩ (m := ∞) (by simp)) z hz).differentiableWithinAt
    (by simp)).hasFDerivWithinAt
  have hsp := hD.clm_comp (hasFDerivWithinAt_const (ContinuousLinearMap.inr ℝ ℝ E) z Ω)
  have ht := hD.clm_apply (hasFDerivWithinAt_const ((1 : ℝ), (0 : E)) z Ω)
  have hspEq := hsp.fderivWithin (hΩ z hz)
  have htEq := ht.fderivWithin (hΩ z hz)
  change fderivWithin ℝ (spatialWithinFDeriv C U f) Ω z = _ at hspEq
  change fderivWithin ℝ (timeWithinFDeriv C U f) Ω z = _ at htEq
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hsym := (hf z hz).isSymmSndFDerivWithinAt htwo hΩ hzcl hz
  change fderivWithin ℝ (spatialWithinFDeriv C U f) Ω z (1, 0) v =
    fderivWithin ℝ (timeWithinFDeriv C U f) Ω z (0, v)
  rw [hspEq, htEq]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.comp_zero, map_zero, zero_add, add_zero,
    ContinuousLinearMap.flip_apply]
  exact hsym (1, 0) (0, v)

theorem mem_closure_interior_Icc_prod {a b s : ℝ} (hab : a < b)
    {U : Set E} (hU : IsOpen U) {x : E} (hs : s ∈ Icc a b) (hx : x ∈ U) :
    (s, x) ∈ closure (interior (Icc a b ×ˢ U)) := by
  rw [interior_prod_eq, interior_Icc, hU.interior_eq, closure_prod_eq,
    closure_Ioo hab.ne]
  exact ⟨hs, subset_closure hx⟩

end MixedDerivative

end PoincareConjecture.M08

