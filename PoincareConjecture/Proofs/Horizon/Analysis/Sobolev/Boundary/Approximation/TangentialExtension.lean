import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.TangentialTests
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private def normalCutoff (n : ℕ) (x : E) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * x 0 - 1)

private theorem normalCutoff_smooth (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalCutoff (d := d) n) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => x 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin d)).contDiff
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hp).sub contDiff_const)

private theorem normalCutoff_norm_le (n : ℕ) (x : E) : ‖normalCutoff n x‖ ≤ 1 := by
  rw [normalCutoff, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

private theorem normalCutoff_tsupport (n : ℕ) :
    tsupport (normalCutoff (d := d) n) ⊆ halfSpace d := by
  have hs : tsupport (normalCutoff (d := d) n) ⊆
      {x : E | 1 ≤ ((n : ℝ) + 1) * x 0} := by
    apply closure_minimal ?_
      (isClosed_le continuous_const
        (continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous))
    intro x hx
    change 1 ≤ ((n : ℝ) + 1) * x 0
    have hn : ¬ ((n : ℝ) + 1) * x 0 - 1 ≤ 0 := by
      intro h
      exact hx (Real.smoothTransition.zero_of_nonpos h)
    linarith
  intro x hx
  have hx' := hs hx
  change 1 ≤ ((n : ℝ) + 1) * x 0 at hx'
  change 0 < x 0
  by_contra! h
  have hmul := mul_nonpos_of_nonneg_of_nonpos
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) h
  linarith

private theorem normalCutoff_partial (n : ℕ) (k : Fin d) (hk : k ≠ 0) (x : E) :
    fderiv ℝ (normalCutoff n) x (EuclideanSpace.single k 1) = 0 := by
  have hi := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin d)).hasFDerivAt
    (x := x)).const_mul ((n : ℝ) + 1)).sub_const 1
  have ho := (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable_one
  have hc := (ho (((n : ℝ) + 1) * x 0 - 1)).hasFDerivAt.comp x hi
  change HasFDerivAt (normalCutoff (d := d) n) _ x at hc
  have h := congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) hc.fderiv
  simpa [ContinuousLinearMap.comp_apply, hk.symm] using h

private theorem normalCutoff_tendsto {x : E} (hx : x ∈ halfSpace d) :
    Tendsto (fun n => normalCutoff n x) atTop (𝓝 1) := by
  change 0 < x 0 at hx
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / x 0)
  have hN' : 2 < (N : ℝ) * x 0 := (div_lt_iff₀ hx).mp hN
  have heq : ∀ᶠ n : ℕ in atTop, normalCutoff n x = 1 := by
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    apply Real.smoothTransition.one_of_one_le
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact tendsto_const_nhds.congr' (heq.mono fun _ hn => hn.symm)

private theorem tendsto_integral_normalCutoff_mul {f : E → ℝ}
    (hf : Integrable f (volume.restrict (halfSpace d))) :
    Tendsto (fun n => ∫ x in halfSpace d, normalCutoff n x * f x) atTop
      (𝓝 (∫ x in halfSpace d, f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact ((normalCutoff_smooth n).continuous.aestronglyMeasurable.restrict).mul
      hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (normalCutoff_norm_le n x) (norm_nonneg _)).trans_eq
        (one_mul _)
  · filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
    simpa using (normalCutoff_tendsto hx).mul_const (f x)



theorem hasWeakPartialDeriv_indicator_halfSpace
    {w g : E → ℝ} (k : Fin d) (hk : k ≠ 0)
    (hw : MemLp w 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d)))
    (hweak : Weak.HasWeakPartialDeriv k g w (halfSpace d)) :
    Weak.HasWeakPartialDeriv k ((halfSpace d).indicator g)
      ((halfSpace d).indicator w) Set.univ := by
  intro φ hφ hc _
  let dφ : E → ℝ := fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)
  have hdcont : Continuous dφ :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcompact : HasCompactSupport dφ := hc.fderiv_apply (𝕜 := ℝ) _
  have hdmem : MemLp dφ 2 (volume.restrict (halfSpace d)) :=
    (hdcont.memLp_of_hasCompactSupport hdcompact).restrict _
  have hφmem : MemLp φ 2 (volume.restrict (halfSpace d)) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict _
  have hleft := tendsto_integral_normalCutoff_mul (hw.integrable_mul hdmem)
  have hright := tendsto_integral_normalCutoff_mul (hg.integrable_mul hφmem)
  have heq (n : ℕ) :
      (∫ x in halfSpace d, normalCutoff n x * (w x * dφ x)) =
        -(∫ x in halfSpace d, normalCutoff n x * (g x * φ x)) := by
    have hprod (x : E) :
        fderiv ℝ (fun y => normalCutoff n y * φ y) x (EuclideanSpace.single k 1) =
          normalCutoff n x * dφ x := by
      have hd := (((normalCutoff_smooth n).differentiable (by simp) x).hasFDerivAt.mul
        ((hφ.differentiable (by simp) x).hasFDerivAt)).fderiv
      have h := congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) hd
      simpa [dφ, Pi.mul_def, normalCutoff_partial n k hk x] using h
    have ht := hweak (fun x => normalCutoff n x * φ x)
      ((normalCutoff_smooth n).mul hφ) hc.mul_left
      (tsupport_mul_subset_left.trans (normalCutoff_tsupport n))
    calc
      _ = ∫ x in halfSpace d,
          w x * fderiv ℝ (fun y => normalCutoff n y * φ y) x
            (EuclideanSpace.single k 1) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only
          rw [hprod]
          ring
      _ = _ := ht
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
  have hlimit : (∫ x in halfSpace d, w x * dφ x) =
      -(∫ x in halfSpace d, g x * φ x) :=
    tendsto_nhds_unique hleft
      (hright.neg.congr' (Eventually.of_forall fun n => (heq n).symm))
  simp only [Measure.restrict_univ]
  have hi (f q : E → ℝ) :
      (∫ x, (halfSpace d).indicator f x * q x) = ∫ x in halfSpace d, f x * q x := by
    rw [← integral_indicator isOpen_halfSpace.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ halfSpace d <;> simp [hx]
  rw [hi w dφ, hi g φ]
  exact hlimit

end Poincare.Analysis.Sobolev.BoundaryTangential
