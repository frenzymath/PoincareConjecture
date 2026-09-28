import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.MetricBump
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.CoefficientRegularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem radialQuadratic_smul (g : RiemannianMetric n M) (p : M)
    (y d : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    radialQuadratic g p y (c • d) = c ^ 2 * radialQuadratic g p y d := by
  simp only [radialQuadratic, real_inner_smul_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem radialQuadratic_eq_inner_inverse (g : RiemannianMetric n M) (p : M)
    (y d : EuclideanSpace ℝ (Fin n)) :
    radialQuadratic g p y d = ⟪d, (chartMetric g p y).inverse (innerSL ℝ d)⟫_ℝ := by
  have hdual : innerSL ℝ d = ∑ i, d i • EuclideanSpace.proj i := by
    ext w
    simp [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      PiLp.proj_apply, mul_comm]
  rw [hdual, map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, inner_smul_right, EuclideanSpace.inner_basisFun_real, mul_comm]

theorem radialQuadratic_pos (g : RiemannianMetric n M) (p : M)
    {y d : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) (hd : d ≠ 0) :
    0 < radialQuadratic g p y d := by
  let B := chartMetric g p y
  let w := B.inverse (innerSL ℝ d)
  have hi : B.IsInvertible := g.isInvertible_chartCoefficients p hy
  have hw : w ≠ 0 := by
    intro hz
    have hdual : innerSL ℝ d = 0 := by
      rw [← hi.self_apply_inverse (innerSL ℝ d)]
      change B w = 0
      rw [hz, map_zero]
    have hzero : inner ℝ d d = 0 := by
      have h := congrArg (fun L => L d) hdual
      simpa using h
    exact hd ((inner_self_eq_zero).mp hzero)
  have hinv : (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have hv : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm y w ≠ 0 := by
    intro hz
    apply hw
    apply hinv.injective
    rw [map_zero]
    exact hz
  have hp := g.pos ((extChartAt (𝓡 n) p).symm y) _ hv
  change 0 < B w w at hp
  have heq : B w w = inner ℝ d w := by
    exact congrArg (fun L => L w) (hi.self_apply_inverse (innerSL ℝ d))
  rw [heq] at hp
  simpa only [radialQuadratic_eq_inner_inverse, w, B] using hp

theorem exists_compact_chart_bounds
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (hJ : UniqueDiffOn ℝ J) (p : M)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKU : K ⊆ J ×ˢ (extChartAt (𝓡 n) p).target)
    {gamma : ℝ → EuclideanSpace ℝ (Fin n)} (hgamma : ContDiff ℝ ∞ gamma) :
    ∃ lam Lam H₀ : ℝ, 0 < lam ∧ lam ≤ Lam ∧ 0 ≤ H₀ ∧
      (∀ z ∈ K, ∀ d : EuclideanSpace ℝ (Fin n),
        lam * ‖d‖ ^ 2 ≤ radialQuadratic (g z.1) p z.2 d ∧
          radialQuadratic (g z.1) p z.2 d ≤ Lam * ‖d‖ ^ 2) ∧
      ∀ z ∈ K, radialTrace (g z.1) p z.2 +
        radialDrift (g z.1) p z.2 (z.2 - gamma z.1) +
        ⟪z.2 - gamma z.1, deriv gamma z.1⟫_ℝ ≤ H₀ := by
  have hi := (contDiffOn_chartMetric_inverse hg p).continuousOn.mono hKU
  have hb := (contDiffOn_chartDrift hg hJ p).continuousOn.mono hKU
  let E := EuclideanSpace ℝ (Fin n)
  let S := sphere (0 : E) 1
  let Q := fun z : (ℝ × E) × E => radialQuadratic (g z.1.1) p z.1.2 z.2
  have hKS : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere 0 1)
  have hQc : ContinuousOn Q (K ×ˢ S) := by
    have hi' : ContinuousOn
        (fun z : (ℝ × E) × E => (chartMetric (g z.1.1) p z.1.2).inverse)
        (K ×ˢ S) :=
      hi.comp continuous_fst.continuousOn (fun _ hz => hz.1)
    simp only [Q, radialQuadratic_eq_inner_inverse]
    exact continuous_snd.continuousOn.inner
      (hi'.clm_apply ((innerSL ℝ).continuous.comp continuous_snd).continuousOn)
  obtain ⟨lam, hlam, hmin⟩ := hKS.exists_forall_le' hQc (a := 0) (by
    intro z hz
    apply radialQuadratic_pos (g z.1.1) p (hKU hz.1).2
    have hn : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    intro hzero
    simp [hzero] at hn)
  obtain ⟨B, hmax⟩ := (hKS.image_of_continuousOn hQc).bddAbove
  have hd : Continuous (fun z : ℝ × E => z.2 - gamma z.1) :=
    continuous_snd.sub (hgamma.continuous.comp continuous_fst)
  let F := fun z : ℝ × E => radialTrace (g z.1) p z.2 +
    radialDrift (g z.1) p z.2 (z.2 - gamma z.1) +
    ⟪z.2 - gamma z.1, deriv gamma z.1⟫_ℝ
  have hFc : ContinuousOn F K := by
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact continuousOn_finsetSum _ fun i _ =>
        continuousOn_const.inner (hi.clm_apply continuousOn_const)
    · exact (hd.continuousOn.inner hb).neg
    · exact (hd.inner ((hgamma.continuous_deriv (by simp)).comp continuous_fst)).continuousOn
  obtain ⟨H₁, hH₁⟩ := (hK.image_of_continuousOn hFc).bddAbove
  refine ⟨lam, max B lam, max H₁ 0, hlam, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro z hz d
    by_cases hd0 : d = 0
    · subst d
      simp [radialQuadratic]
    · let η := ‖d‖⁻¹ • d
      have hη : η ∈ S := mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hd0)
      have hscale : ‖d‖ • η = d := smul_inv_smul₀ (norm_ne_zero_iff.mpr hd0) d
      have hhom : radialQuadratic (g z.1) p z.2 d =
          ‖d‖ ^ 2 * radialQuadratic (g z.1) p z.2 η := by
        rw [← radialQuadratic_smul, hscale]
      have hlo := mul_le_mul_of_nonneg_left (hmin (z, η) ⟨hz, hη⟩) (sq_nonneg ‖d‖)
      have hup : Q (z, η) ≤ max B lam :=
        (hmax (mem_image_of_mem Q (show (z, η) ∈ K ×ˢ S from ⟨hz, hη⟩))).trans
          (le_max_left _ _)
      have hup' := mul_le_mul_of_nonneg_left hup (sq_nonneg ‖d‖)
      constructor
      · simpa only [Q, hhom, mul_comm] using hlo
      · simpa only [Q, hhom, mul_comm] using hup'
  · intro z hz
    exact (hH₁ (mem_image_of_mem F hz)).trans (le_max_left _ _)

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
