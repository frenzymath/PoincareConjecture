import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityACComposition
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coneCoordinates (r : ℝ) (v0 : E) (v : ℝ → E) (s t : ℝ) : E :=
  v0 + (s / r) • (v t - v0)

theorem coneCoordinates_endpoints {r : ℝ} (hr : r ≠ 0) (v0 : E) (v : ℝ → E)
    {a b : ℝ} (hv : v a = v b) :
    (∀ t, coneCoordinates r v0 v 0 t = v0) ∧
      (∀ t, coneCoordinates r v0 v r t = v t) ∧
      ∀ s, coneCoordinates r v0 v s a = coneCoordinates r v0 v s b := by
  constructor
  · intro t
    simp only [coneCoordinates, zero_div, zero_smul, add_zero]
  constructor
  · intro t
    simp only [coneCoordinates, div_self hr, one_smul, add_sub_cancel]
  · intro s
    rw [coneCoordinates, coneCoordinates, hv]

theorem coneCoordinates_mem_closedBall {r ρ s t : ℝ} (hr : 0 < r)
    {v0 : E} {v : ℝ → E} (h0 : v0 ∈ closedBall 0 ρ)
    (hv : v t ∈ closedBall 0 ρ) (hs : s ∈ Icc 0 r) :
    coneCoordinates r v0 v s t ∈ closedBall 0 ρ := by
  have ha : 0 ≤ s / r := div_nonneg hs.1 hr.le
  have hb : s / r ≤ 1 := (div_le_one hr).mpr hs.2
  have h := (convex_closedBall (0 : E) ρ) h0 hv (sub_nonneg.mpr hb) ha
    (by ring : 1 - s / r + s / r = 1)
  convert h using 1
  simp only [coneCoordinates, sub_smul, one_smul, smul_sub]
  abel

theorem coneCoordinates_radial_hasDerivAt (r : ℝ) (v0 : E) (v : ℝ → E) (s t : ℝ) :
    HasDerivAt (fun q => coneCoordinates r v0 v q t) (r⁻¹ • (v t - v0)) s := by
  simpa only [coneCoordinates, one_div, id_eq] using
    (((hasDerivAt_id s).div_const r).smul_const (v t - v0)).const_add v0

theorem coneCoordinates_angular_AC {v : ℝ → E} {a b : ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b) (r : ℝ) (v0 : E) (s : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => coneCoordinates r v0 v s t) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => v0) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  exact hc.fun_add ((hv.fun_sub hc).const_smul (s / r))

theorem coneCoordinates_angular_increment {v d : ℝ → E} {a b : ℝ}
    (hinc : ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, v u - v t = ∫ θ in t..u, d θ)
    (r : ℝ) (v0 : E) (s : ℝ) :
    ∀ t ∈ Icc a b, ∀ u ∈ Icc a b,
      coneCoordinates r v0 v s u - coneCoordinates r v0 v s t =
        ∫ θ in t..u, (s / r) • d θ := by
  intro t ht u hu
  rw [intervalIntegral.integral_smul, ← hinc t ht u hu]
  simp only [coneCoordinates, smul_sub]
  abel

end PoincareConjecture.M65Interior
