import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.ReactionInvariance
import PoincareConjecture.Definitions.Ch04.Pinching

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem scalar_lower_bound_persists_of_M04
    [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : ∀ x : M,
      -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x) :
    ∀ t ∈ Set.Ico a b, ∀ x : M,
      -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x := by
  intro t ht x
  exact hM04.normalized_scalar_lower_bound M a b F ha hab hinit t ht x

theorem scalar_region_persists_of_ordered_reaction
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lam mu nu : ℝ → ℝ}
    (hlam : ContinuousOn lam (Set.Icc a b))
    (hmu : ContinuousOn mu (Set.Icc a b))
    (hnu : ContinuousOn nu (Set.Icc a b))
    (hord : ∀ t ∈ Set.Icc a b, mu t ≤ lam t ∧ nu t ≤ mu t)
    (hdlam : ∀ t ∈ Set.Ioo a b,
      HasDerivAt lam (lam t ^ 2 + mu t * nu t) t)
    (hdmu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt mu (mu t ^ 2 + lam t * nu t) t)
    (hdnu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt nu (nu t ^ 2 + lam t * mu t) t)
    (hinit : (lam a + mu a + nu a, max (-nu a) 0) ∈
      Poincare.HamiltonIvey.scalarRegion a) :
    ∀ t ∈ Set.Icc a b,
      (lam t + mu t + nu t, max (-nu t) 0) ∈
        Poincare.HamiltonIvey.scalarRegion t := by
  exact Poincare.HamiltonIvey.reaction_invariance ha hab hlam hmu hnu hord
    hdlam hdmu hdnu hinit

theorem initial_scalar_region_of_pinching
    {a S X : ℝ} (ha : 0 ≤ a)
    (htrace : -6 / (1 + 4 * a) ≤ 2 * S)
    (hlog : 0 < X →
      2 * X * (Real.log X + Real.log (1 + a) - 3) ≤ 2 * S) :
    (S, X) ∈ Poincare.HamiltonIvey.scalarRegion a := by
  have hden4 : 0 < 1 + 4 * a := by linarith
  have htrace_mul : -6 ≤ 2 * S * (1 + 4 * a) :=
    (div_le_iff₀ hden4).mp htrace
  have htrace' : -3 / (1 + 4 * a) ≤ S := by
    apply (div_le_iff₀ hden4).2
    nlinarith [htrace_mul]
  rw [Poincare.HamiltonIvey.mem_scalarRegion_iff ha]
  by_cases hcut : Poincare.HamiltonIvey.cutoff a ≤ X
  · rw [Poincare.HamiltonIvey.clippedBarrier, max_eq_right hcut]
    rw [Poincare.HamiltonIvey.logBarrier]
    have hX : 0 < X :=
      (Poincare.HamiltonIvey.cutoff_pos ha).trans_le hcut
    nlinarith [hlog hX]
  · rw [Poincare.HamiltonIvey.clippedBarrier,
      max_eq_left (le_of_not_ge hcut),
      Poincare.HamiltonIvey.logBarrier_cutoff ha]
    have hden1 : 0 < 1 + a := by linarith
    have hhorizontal : -3 / (1 + a) ≤ -3 / (1 + 4 * a) := by
      apply (div_le_div_iff₀ hden1 hden4).2
      nlinarith
    exact hhorizontal.trans htrace'

theorem logarithmic_pinching_of_scalar_region
    {t lam mu nu : ℝ} (ht : 0 ≤ t) (hmu : mu ≤ lam) (hnu : nu ≤ mu)
    (hregion : (lam + mu + nu, max (-nu) 0) ∈
      Poincare.HamiltonIvey.scalarRegion t)
    (hX : 0 < max (-nu) 0) :
    2 * max (-nu) 0 * (Real.log (max (-nu) 0) + Real.log (1 + t) - 3) ≤
      2 * (lam + mu + nu) := by
  have htrace : -3 / (1 + t) ≤ lam + mu + nu := hregion.1
  have hmem := (Poincare.HamiltonIvey.mem_scalarRegion_iff ht).mp hregion
  have hXeq : max (-nu) 0 = -nu := by
    have hneg : 0 < -nu := by
      by_contra h
      have hz : max (-nu) 0 = 0 := max_eq_right (le_of_not_gt h)
      linarith
    exact max_eq_left hneg.le
  have hsum : -3 * max (-nu) 0 ≤ lam + mu + nu := by
    rw [hXeq]
    linarith
  by_cases hsmall : max (-nu) 0 ≤ 1 / (1 + t)
  · have hlogtime : Real.log (max (-nu) 0) + Real.log (1 + t) ≤ 0 := by
      have hden : 0 < 1 + t := by linarith
      rw [← Real.log_mul (ne_of_gt hX) hden.ne']
      exact Real.log_nonpos (mul_nonneg (le_of_lt hX) hden.le)
        ((le_div_iff₀ hden).mp hsmall)
    have hprod : max (-nu) 0 *
        (Real.log (max (-nu) 0) + Real.log (1 + t) - 3) ≤
        -3 * max (-nu) 0 := by
      have hfactor :
          Real.log (max (-nu) 0) + Real.log (1 + t) - 3 ≤ 0 := by
        linarith
      have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hX) hfactor
      nlinarith [hprod]
    nlinarith
  · have hfirst : 1 / (1 + t) < max (-nu) 0 := lt_of_not_ge hsmall
    by_cases hlarge : Poincare.HamiltonIvey.cutoff t ≤ max (-nu) 0
    · have hlog := hmem
      rw [Poincare.HamiltonIvey.clippedBarrier, max_eq_right hlarge,
        Poincare.HamiltonIvey.logBarrier] at hlog
      nlinarith
    · have hbetween : max (-nu) 0 ≤ Poincare.HamiltonIvey.cutoff t :=
        le_of_not_ge hlarge
      have hconv := ConvexOn.le_max_of_mem_Icc
        (Poincare.HamiltonIvey.strictConvexOn_logBarrier t).convexOn
        (Set.mem_Ici.mpr (by positivity))
        (Set.mem_Ici.mpr (Poincare.HamiltonIvey.cutoff_pos ht).le)
        ⟨hfirst.le, hbetween⟩
      have hbar : Poincare.HamiltonIvey.logBarrier t (max (-nu) 0) ≤
          -3 / (1 + t) := by
        rw [Poincare.HamiltonIvey.logBarrier_first ht,
          Poincare.HamiltonIvey.logBarrier_cutoff ht, max_self] at hconv
        exact hconv
      have hlog := hbar.trans htrace
      rw [Poincare.HamiltonIvey.logBarrier] at hlog
      nlinarith

theorem logarithmic_pinching_of_ordered_reaction
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {lam mu nu : ℝ → ℝ}
    (hlam : ContinuousOn lam (Set.Icc a b))
    (hmu : ContinuousOn mu (Set.Icc a b))
    (hnu : ContinuousOn nu (Set.Icc a b))
    (hord : ∀ t ∈ Set.Icc a b, mu t ≤ lam t ∧ nu t ≤ mu t)
    (hdlam : ∀ t ∈ Set.Ioo a b,
      HasDerivAt lam (lam t ^ 2 + mu t * nu t) t)
    (hdmu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt mu (mu t ^ 2 + lam t * nu t) t)
    (hdnu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt nu (nu t ^ 2 + lam t * mu t) t)
    (hinit : (lam a + mu a + nu a, max (-nu a) 0) ∈
      Poincare.HamiltonIvey.scalarRegion a) :
    ∀ t ∈ Set.Ico a b,
      0 < max (-nu t) 0 →
        2 * max (-nu t) 0 *
            (Real.log (max (-nu t) 0) + Real.log (1 + t) - 3) ≤
          2 * (lam t + mu t + nu t) := by
  intro t ht hX
  have htcc : t ∈ Set.Icc a b := ⟨ht.1, ht.2.le⟩
  exact logarithmic_pinching_of_scalar_region (ha.trans ht.1)
    (hord t htcc).1 (hord t htcc).2
    (scalar_region_persists_of_ordered_reaction ha hab.le hlam hmu hnu
      hord hdlam hdmu hdnu hinit t htcc) hX

theorem flow_log_pinching_of_ordered_reaction
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (lam mu nu : M → ℝ → ℝ)
    (hlam : ∀ x : M, ContinuousOn (lam x) (Set.Icc a b))
    (hmu : ∀ x : M, ContinuousOn (mu x) (Set.Icc a b))
    (hnu : ∀ x : M, ContinuousOn (nu x) (Set.Icc a b))
    (hord : ∀ x : M, ∀ t ∈ Set.Icc a b,
      mu x t ≤ lam x t ∧ nu x t ≤ mu x t)
    (hdlam : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (lam x) (lam x t ^ 2 + mu x t * nu x t) t)
    (hdmu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (mu x) (mu x t ^ 2 + lam x t * nu x t) t)
    (hdnu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (nu x) (nu x t ^ 2 + lam x t * mu x t) t)
    (hinit : ∀ x : M, (lam x a + mu x a + nu x a, max (-nu x a) 0) ∈
      Poincare.HamiltonIvey.scalarRegion a) :
    ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < max (-nu x t) 0 →
        2 * max (-nu x t) 0 *
            (Real.log (max (-nu x t) 0) + Real.log (1 + t) - 3) ≤
          2 * (lam x t + mu x t + nu x t) := by
  intro t ht x hX
  exact logarithmic_pinching_of_ordered_reaction ha hab
    (hlam x) (hmu x) (hnu x) (hord x) (hdlam x) (hdmu x) (hdnu x)
    (hinit x) t ht hX

theorem geometric_log_pinching_of_ordered_reaction
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (F : RicciFlow 3 M (Set.Ico a b))
    (lam mu nu : M → ℝ → ℝ)
    (hlam : ∀ x : M, ContinuousOn (lam x) (Set.Icc a b))
    (hmu : ∀ x : M, ContinuousOn (mu x) (Set.Icc a b))
    (hnu : ∀ x : M, ContinuousOn (nu x) (Set.Icc a b))
    (hord : ∀ x : M, ∀ t ∈ Set.Icc a b,
      mu x t ≤ lam x t ∧ nu x t ≤ mu x t)
    (hdlam : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (lam x) (lam x t ^ 2 + mu x t * nu x t) t)
    (hdmu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (mu x) (mu x t ^ 2 + lam x t * nu x t) t)
    (hdnu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (nu x) (nu x t ^ 2 + lam x t * mu x t) t)
    (hinit : ∀ x : M, (lam x a + mu x a + nu x a, max (-nu x a) 0) ∈
      Poincare.HamiltonIvey.scalarRegion a)
    (hleast : ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).leastSectionalCurvature x = nu x t)
    (hscalar : ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).scalarCurvature x = 2 * (lam x t + mu x t + nu x t)) :
    ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < max (-((F.connection t).leastSectionalCurvature x)) 0 →
        2 * max (-((F.connection t).leastSectionalCurvature x)) 0 *
            (Real.log (max (-((F.connection t).leastSectionalCurvature x)) 0) +
              Real.log (1 + t) - 3) ≤
          (F.connection t).scalarCurvature x := by
  intro t ht x hX
  rw [hleast t ht x, hscalar t ht x]
  exact flow_log_pinching_of_ordered_reaction ha hab lam mu nu hlam hmu hnu hord
    hdlam hdmu hdnu hinit t ht x (by simpa [hleast t ht x] using hX)

theorem geometric_log_pinching_of_initial_data
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (lam mu nu : M → ℝ → ℝ)
    (hlam : ∀ x : M, ContinuousOn (lam x) (Set.Icc a b))
    (hmu : ∀ x : M, ContinuousOn (mu x) (Set.Icc a b))
    (hnu : ∀ x : M, ContinuousOn (nu x) (Set.Icc a b))
    (hord : ∀ x : M, ∀ t ∈ Set.Icc a b,
      mu x t ≤ lam x t ∧ nu x t ≤ mu x t)
    (hdlam : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (lam x) (lam x t ^ 2 + mu x t * nu x t) t)
    (hdmu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (mu x) (mu x t ^ 2 + lam x t * nu x t) t)
    (hdnu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (nu x) (nu x t ^ 2 + lam x t * mu x t) t)
    (htrace : ∀ x : M, -6 / (1 + 4 * a) ≤
      2 * (lam x a + mu x a + nu x a))
    (hlog : ∀ x : M, 0 < max (-nu x a) 0 →
      2 * max (-nu x a) 0 *
          (Real.log (max (-nu x a) 0) + Real.log (1 + a) - 3) ≤
        2 * (lam x a + mu x a + nu x a)) :
    ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < max (-nu x t) 0 →
        2 * max (-nu x t) 0 *
            (Real.log (max (-nu x t) 0) + Real.log (1 + t) - 3) ≤
          2 * (lam x t + mu x t + nu x t) := by
  have hinit : ∀ x : M,
      (lam x a + mu x a + nu x a, max (-nu x a) 0) ∈
        Poincare.HamiltonIvey.scalarRegion a := by
    intro x
    exact initial_scalar_region_of_pinching ha (htrace x) (hlog x)
  exact flow_log_pinching_of_ordered_reaction ha hab lam mu nu hlam hmu hnu hord
    hdlam hdmu hdnu hinit

end PoincareConjecture
