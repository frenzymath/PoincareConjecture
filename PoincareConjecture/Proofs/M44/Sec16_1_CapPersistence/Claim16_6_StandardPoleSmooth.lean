import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_StandardPole
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M44

open M36 RiemannianMetric

theorem continuous_standard_tangentNorm (g₀ : StandardInitialMetric) :
    Continuous (fun v : StandardCapSpace => g₀.metric.tangentNorm 0 v) := by
  unfold tangentNorm
  exact Real.continuous_sqrt.comp
    ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)

theorem standardRadialExponential_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (standardRadialExponential g₀) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  let R := g₀.metric.tangentNorm 0 v + 1
  have hR : 0 < R := by
    dsimp only [R, tangentNorm]
    linarith [Real.sqrt_nonneg (g₀.metric.inner 0 v v)]
  have hcompact : IsCompact (closure (g₀.metric.ball 0 R)) := by
    rw [standard_closure_ball g₀ hR]
    exact standard_closed_ball_compact g₀ hR.le
  obtain ⟨e, he, _, _, hexp, _, _⟩ :=
    g₀.metric.exists_smooth_exponential_with_ball_images 0 hR hcompact
  have heq := standard_exponential_eq_radial g₀ hexp
  have hV : IsOpen {w : StandardCapSpace | g₀.metric.tangentNorm 0 w < R} :=
    isOpen_lt (continuous_standard_tangentNorm g₀) continuous_const
  have hv : g₀.metric.tangentNorm 0 v < R := by dsimp only [R]; linarith
  have hs : ContDiffAt ℝ ∞ e v :=
    contMDiffAt_iff_contDiffAt.mp ((he v hv).contMDiffAt (hV.mem_nhds hv))
  apply hs.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hv] with w hw
  exact (heq hw).symm

theorem standardRadialExponential_hasFDerivAt_zero (g₀ : StandardInitialMetric) :
    HasFDerivAt (standardRadialExponential g₀)
      (ContinuousLinearMap.id ℝ StandardCapSpace) 0 := by
  have hcompact : IsCompact (closure (g₀.metric.ball 0 1)) := by
    rw [standard_closure_ball g₀ zero_lt_one]
    exact standard_closed_ball_compact g₀ zero_le_one
  obtain ⟨e, _, _, hd, hexp, _, _⟩ :=
    g₀.metric.exists_smooth_exponential_with_ball_images 0 zero_lt_one hcompact
  have heq := standard_exponential_eq_radial g₀ hexp
  have hV : IsOpen {w : StandardCapSpace | g₀.metric.tangentNorm 0 w < 1} :=
    isOpen_lt (continuous_standard_tangentNorm g₀) continuous_const
  have hzero : g₀.metric.tangentNorm 0 0 < 1 := by simp [tangentNorm]
  have hd' : HasFDerivAt e (ContinuousLinearMap.id ℝ StandardCapSpace) 0 := by
    simpa only [StandardCapSpace, extChartAt_self_eq, modelWithCornersSelf_coe, id_eq]
      using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hzero] with w hw
  exact (heq hw).symm

theorem standardRadialLogarithm_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (standardRadialLogarithm g₀) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have hf := (standardRadialExponential_contDiff g₀).contDiffAt (x := 0)
    have hd : HasFDerivAt (standardRadialExponential g₀)
        (ContinuousLinearEquiv.refl ℝ StandardCapSpace).toContinuousLinearMap 0 :=
      standardRadialExponential_hasFDerivAt_zero g₀
    have hstrict := hf.hasStrictFDerivAt' hd (by simp)
    have hi := hf.to_localInverse hd (by simp)
    have heq := hstrict.localInverse_unique
      (Eventually.of_forall (standardRadialLogarithm_exponential g₀))
    simpa only [standardRadialExponential_zero] using hi.congr_of_eventuallyEq heq
  · have hn : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x := contDiffAt_norm ℝ hx
    exact (((radialArclength_contDiff g₀).contDiffAt.comp x hn).div_const
      (radialSpeed g₀ 0)).smul ((hn.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id)

noncomputable def standardRadialDiffeomorph (g₀ : StandardInitialMetric) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := standardRadialExponential g₀
  invFun := standardRadialLogarithm g₀
  left_inv := standardRadialLogarithm_exponential g₀
  right_inv := standardRadialExponential_logarithm g₀
  contMDiff_toFun := (standardRadialExponential_contDiff g₀).contMDiff
  contMDiff_invFun := (standardRadialLogarithm_contDiff g₀).contMDiff

end PoincareConjecture.M44
