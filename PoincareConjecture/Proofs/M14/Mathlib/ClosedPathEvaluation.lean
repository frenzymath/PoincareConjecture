import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc










set_option autoImplicit false

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}




noncomputable def closedPathEvaluation (hab : a ≤ b) (Φ : P → C(Icc a b, F)) (z : P × ℝ) : F :=
  Φ z.1 (projIcc a b hab z.2)

omit [NormedSpace ℝ P] [NormedSpace ℝ F] in


theorem continuousOn_closedPathEvaluation (hab : a ≤ b) {U : Set P}
    {Φ : P → C(Icc a b, F)} (hΦ : ContinuousOn Φ U) :
    ContinuousOn (closedPathEvaluation hab Φ) (U ×ˢ univ) := by
  have hπ : Continuous (projIcc a b hab) := continuous_projIcc
  exact continuous_eval.comp_continuousOn
    ((hΦ.comp continuous_fst.continuousOn (fun _ hz => hz.1)).prodMk
      (hπ.comp continuous_snd).continuousOn)

variable [FiniteDimensional ℝ P]




theorem hasFDerivWithinAt_closedPathEvaluation (hab : a ≤ b)
    {Φ : P → C(Icc a b, F)} {x : P} {A : P →L[ℝ] C(Icc a b, F)}
    (hΦ : HasFDerivAt Φ A x) (t : Icc a b) {v : F}
    (ht : HasDerivWithinAt (fun s => closedPathEvaluation hab Φ (x, s)) v
      (Icc a b) t.val) :
    HasFDerivWithinAt (closedPathEvaluation hab Φ)
      (((ContinuousMap.evalCLM (R := ℝ) t).comp A).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight v)) (univ ×ˢ Icc a b) (x, t.val) := by
  let B : ℝ → P →L[ℝ] F := fun s => (ContinuousMap.evalCLM (R := ℝ)
    (projIcc a b hab s)).comp A
  have hB : Continuous B := continuous_clm_apply.mpr fun h =>
    (A h).continuous.comp continuous_projIcc
  have hpt : projIcc a b hab t.val = t := projIcc_of_mem hab t.property
  have hBt : B t.val = (ContinuousMap.evalCLM (R := ℝ) t).comp A := by
    dsimp only [B]
    rw [hpt]
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  have hp := (hasFDerivAt_iff_isLittleO.mp hΦ).bound he
  have htime := ht.isLittleO.bound he
  have hb : ∀ᶠ s in 𝓝 t.val, ‖B s - B t.val‖ ≤ ε / 3 := by
    filter_upwards [hB.continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (B t.val) he)] with s hs
    exact (show ‖B s - B t.val‖ < ε / 3 by simpa only [Metric.mem_ball, dist_eq_norm] using hs).le
  rw [nhdsWithin_prod_eq, nhdsWithin_univ]
  filter_upwards [tendsto_fst.eventually hp, tendsto_snd.eventually htime,
    tendsto_snd.eventually (hb.filter_mono nhdsWithin_le_nhds)] with z hz ht' hb'
  have hxnorm : ‖z.1 - x‖ ≤ ‖z - (x, t.val)‖ := by
    exact le_max_left _ _
  have htnorm : ‖z.2 - t.val‖ ≤ ‖z - (x, t.val)‖ := by
    exact le_max_right _ _
  have hr₁ : ‖Φ z.1 (projIcc a b hab z.2) - Φ x (projIcc a b hab z.2) -
      A (z.1 - x) (projIcc a b hab z.2)‖ ≤ (ε / 3) * ‖z - (x, t.val)‖ :=
    ((Φ z.1 - Φ x - A (z.1 - x)).norm_coe_le_norm _).trans
      (hz.trans (mul_le_mul_of_nonneg_left hxnorm he.le))
  have hr₂ : ‖A (z.1 - x) (projIcc a b hab z.2) - A (z.1 - x) t‖ ≤
      (ε / 3) * ‖z - (x, t.val)‖ := by
    have h := (B z.2 - B t.val).le_opNorm (z.1 - x)
    rw [hBt] at h
    exact h.trans (mul_le_mul (by simpa only [hBt] using hb') hxnorm (norm_nonneg _) he.le)
  have hr₃ : ‖Φ x (projIcc a b hab z.2) - Φ x t - (z.2 - t.val) • v‖ ≤
      (ε / 3) * ‖z - (x, t.val)‖ := by
    simp only [closedPathEvaluation, hpt] at ht'
    exact ht'.trans (mul_le_mul_of_nonneg_left htnorm he.le)
  have heq : closedPathEvaluation hab Φ z - closedPathEvaluation hab Φ (x, t.val) -
      (((ContinuousMap.evalCLM (R := ℝ) t).comp A).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight v)) (z - (x, t.val)) =
      (Φ z.1 (projIcc a b hab z.2) - Φ x (projIcc a b hab z.2) -
        A (z.1 - x) (projIcc a b hab z.2)) +
      (A (z.1 - x) (projIcc a b hab z.2) - A (z.1 - x) t) +
      (Φ x (projIcc a b hab z.2) - Φ x t - (z.2 - t.val) • v) := by
    simp only [closedPathEvaluation, hpt, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      Prod.fst_sub, Prod.snd_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    ((add_le_add (add_le_add hr₁ hr₂) hr₃).trans_eq (by ring)))

end PoincareConjecture.M14
