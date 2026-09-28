import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_FullCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MetricGerm
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

private theorem short_normal_strip_properties
    (N : IntrinsicAnnulus)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hu : ContDiff ℝ ∞ u)
    (hnormal : ∀ a,
      N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
      N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
        (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
      0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a))
    (hboundary : ∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a)
    (hvelocity : ∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ Icc 0 rampPeriod, ∀ t ∈ Icc 0 r,
      Function.Injective (fderiv ℝ u (a, t)) ∧
      u (a, t) ∈ standardAnnulusDomain ∧
      (0 < t → 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) := by
  let q : ℝ × ℝ → ℝ := fun z => ‖u z‖ ^ 2
  have hq : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp hu
  let D : ℝ × ℝ → ℝ := fun z => fderiv ℝ q z (0, 1)
  have hD : Continuous D := (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  let V : Set (ℝ × ℝ) := interior {z | Function.Injective (fderiv ℝ u z)}
  let U : Set (ℝ × ℝ) := V ∩ {z | 0 < D z} ∩ {z | ‖u z‖ < 2}
  have hU : IsOpen U :=
    (isOpen_interior.inter (isOpen_lt continuous_const hD)).inter
      (isOpen_lt hu.continuous.norm continuous_const)
  have hnorm (a : ℝ) : ‖u (a, 0)‖ = 1 := by
    rw [hboundary]
    have h := m64Intrinsic_boundary_self_inner 1 a
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 a)]
  have hcomp (a t : ℝ) : HasDerivAt (fun s => q (a, s)) (D (a, t)) t := by
    exact (hq.differentiable (by simp) (a, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t a).prodMk (hasDerivAt_id t))
  let K : Set (ℝ × ℝ) := Icc 0 rampPeriod ×ˢ {0}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hKU : K ⊆ U := by
    rintro ⟨a, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    obtain ⟨W, hW, haW, hWreg⟩ :=
      m64Intrinsic_normal_variation_regular_neighborhood N (by norm_num)
        hu.contDiffAt (Eventually.of_forall hboundary) (hvelocity a)
        (hnormal a).1 (hnormal a).2.1
    have hreg : (a, 0) ∈ V :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hW.mem_nhds haW) hWreg)
    have hrad : 0 < D (a, 0) := by
      have hd := (hcomp a 0).unique (hvelocity a).norm_sq
      rw [hd, hboundary]
      exact mul_pos (by norm_num) (hnormal a).2.2
    exact ⟨⟨hreg, hrad⟩, by change ‖u (a, 0)‖ < 2; rw [hnorm]; norm_num⟩
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hstrip (a : ℝ) (ha : a ∈ Icc 0 rampPeriod) (t : ℝ) (ht : t ∈ Icc 0 r) :
      (a, t) ∈ U := by
    apply hrU
    apply Metric.mem_cthickening_of_dist_le (a, t) (a, 0) r K ⟨ha, rfl⟩
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
    exact max_le hr.le (by rw [abs_of_nonneg ht.1]; exact ht.2)
  refine ⟨r, hr, ?_⟩
  intro a ha t ht
  have hhere := hstrip a ha t ht
  have hmono : StrictMonoOn (fun s => q (a, s)) (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hq.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    intro s hs
    change 0 < deriv (fun t => q (a, t)) s
    rw [(hcomp a s).deriv]
    exact (hstrip a ha s (interior_subset hs)).1.2
  have hlower : 1 ≤ ‖u (a, t)‖ := by
    have h := hmono.monotoneOn (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.le⟩) ht ht.1
    change ‖u (a, 0)‖ ^ 2 ≤ ‖u (a, t)‖ ^ 2 at h
    rw [hnorm] at h
    nlinarith [norm_nonneg (u (a, t))]
  refine ⟨interior_subset hhere.1.1, ⟨hlower, hhere.2.le⟩, ?_⟩
  intro hpos
  have h := hmono (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.le⟩) ht hpos
  change ‖u (a, 0)‖ ^ 2 < ‖u (a, t)‖ ^ 2 at h
  rw [hnorm] at h
  exact ⟨by nlinarith [norm_nonneg (u (a, t))], hhere.2⟩

theorem m64Intrinsic_exists_embedded_normal_collar (N : IntrinsicAnnulus) :
    ∃ (normal : ℝ → AnnulusCoordinates) (u : ℝ × ℝ → AnnulusCoordinates) (r : ℝ),
      0 < r ∧ r ≤ 1 ∧ ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      (∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0) ∧
      InjOn u (Ico 0 rampPeriod ×ˢ Icc 0 r) ∧
      (∀ a ∈ Icc 0 rampPeriod, ∀ t ∈ Icc 0 r,
        Function.Injective (fderiv ℝ u (a, t)) ∧
        u (a, t) ∈ standardAnnulusDomain ∧
        (0 < t → 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2)) ∧
      ∀ a ∈ Icc 0 rampPeriod, N.metric.IsGeodesicOn (fun t => u (a, t)) (Icc 0 r) := by
  obtain ⟨G, normal, u, hG, hn, hu, hnormal, hboundary, hvelocity, hgeo,
    r₀, hr₀, hr₀one, hinj⟩ := m64Intrinsic_exists_embedded_full_normal_collar N
  obtain ⟨r₁, hr₁, hproperties⟩ :=
    short_normal_strip_properties N hu hnormal hboundary hvelocity
  let r := min r₀ r₁
  have hr0 : r ≤ r₀ := min_le_left _ _
  have hr1 : r ≤ r₁ := min_le_right _ _
  refine ⟨normal, u, r, lt_min hr₀ hr₁, hr0.trans hr₀one, hn, hu, hnormal,
    hboundary, hvelocity, hinj.mono ?_, ?_, ?_⟩
  · exact prod_mono_right (Icc_subset_Icc_right hr0)
  · intro a ha t ht
    exact hproperties a ha t ⟨ht.1, ht.2.trans hr1⟩
  · intro a ha
    apply m64Intrinsic_geodesic_of_metric_germ G N.metric
      (fun t ht => hgeo a t ⟨ht.1, ht.2.trans (hr0.trans hr₀one)⟩)
    intro t ht
    exact hG _ (hproperties a ha t ⟨ht.1, ht.2.trans hr1⟩).2.1

end PoincareConjecture
