import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_SmoothNormalMap
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalRegularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Thickening














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture



theorem m64Intrinsic_boundary_injOn_short_arc {a b : ℝ}
    (hab : b - a < rampPeriod) :
    InjOn (intrinsicAnnulusBoundary 1) (Icc a b) := by
  intro x hx y hy hxy
  apply Circle.exp_injOn_Icc hab hx hy
  apply Subtype.ext
  apply Complex.ext
  · have h := congrArg (fun z : AnnulusCoordinates => z 0) hxy
    simp only [intrinsicAnnulusBoundary, one_mul, Matrix.cons_val_zero] at h
    simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using h
  · have h := congrArg (fun z : AnnulusCoordinates => z 1) hxy
    simp only [intrinsicAnnulusBoundary, one_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h
    simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using h

private theorem normal_map_locally_injective
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    {z : ℝ × ℝ} (hi : Function.Injective (fderiv ℝ u z)) :
    ∃ U ∈ 𝓝 z, InjOn u U := by
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ AnnulusCoordinates := by
    simp
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  let A : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates :=
    (LinearEquiv.ofBijective (fderiv ℝ u z).toLinearMap
      ⟨hi, hs⟩).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ u z := rfl
  have hd : HasFDerivAt u A.toContinuousLinearMap z := by
    rw [hA]
    exact (hu.differentiable (by simp) z).hasFDerivAt
  let F := hu.contDiffAt.toOpenPartialHomeomorph u hd (by simp)
  refine ⟨F.source, F.open_source.mem_nhds
    (hu.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)), ?_⟩
  exact F.injOn




theorem m64Intrinsic_normal_arc_has_embedded_collar
    (N : IntrinsicAnnulus)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hu : ContDiff ℝ ∞ u)
    (hboundary : ∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s)
    (hvelocity : ∀ s, HasDerivAt (fun t => u (s, t)) (normal s) 0)
    (hunit : ∀ s, N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s) (normal s) = 1)
    (horth : ∀ s, N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s)
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) s) = 0)
    {a b : ℝ} (hab : b - a < rampPeriod) :
    ∃ r : ℝ, 0 < r ∧ InjOn u (Icc a b ×ˢ Icc (-r) r) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ {0}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hKinj : InjOn u K := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩ ⟨y, s⟩ ⟨hy, hs⟩ heq
    have ht0 : t = 0 := ht
    have hs0 : s = 0 := hs
    subst t
    subst s
    have hxy : x = y := m64Intrinsic_boundary_injOn_short_arc hab hx hy
      (by simpa only [hboundary] using heq)
    subst y
    rfl
  have hlocal : ∀ z ∈ K, ∃ U ∈ 𝓝 z, InjOn u U := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    apply normal_map_locally_injective hu
    exact m64Intrinsic_normal_variation_initial_fderiv_injective N (by norm_num)
      (hu.differentiable (by simp) (x, 0))
      (Eventually.of_forall hboundary) (hvelocity x) (hunit x) (horth x)
  obtain ⟨U, hU, hKU, hUinj⟩ := hKinj.exists_isOpen_superset hK
    (fun z _ => hu.continuous.continuousAt) hlocal
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨r, hr, hUinj.mono ?_⟩
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  apply hrU
  apply Metric.mem_cthickening_of_dist_le (x, t) (x, 0) r K ⟨hx, rfl⟩
  simp only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
  exact max_le hr.le (abs_le.mpr ht)




theorem m64Intrinsic_exists_embedded_normal_arc_collars (N : IntrinsicAnnulus) :
    ∃ (G : RiemannianMetric 2 AnnulusCoordinates)
      (normal : ℝ → AnnulusCoordinates) (u : ℝ × ℝ → AnnulusCoordinates),
      (∀ p ∈ standardAnnulusDomain,
        G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients) ∧
      ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      (∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0) ∧
      (∀ a, G.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) 1)) ∧
      ∀ a b : ℝ, b - a < rampPeriod →
        ∃ r : ℝ, 0 < r ∧ InjOn u (Icc a b ×ˢ Icc (-r) r) := by
  obtain ⟨G, normal, u, hG, hn, hu, hnormal, hboundary, hvelocity, hgeo⟩ :=
    m64Intrinsic_exists_smooth_extended_normal_map N
  refine ⟨G, normal, u, hG, hn, hu, hnormal, hboundary, hvelocity, hgeo, ?_⟩
  intro a b hab
  exact m64Intrinsic_normal_arc_has_embedded_collar N hu hboundary hvelocity
    (fun s => (hnormal s).1) (fun s => (hnormal s).2.1) hab

end PoincareConjecture
