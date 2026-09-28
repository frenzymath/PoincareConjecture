import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingSegment
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingTransport
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuedPolar
















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_varying_focusing_arc_length_le_turning
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (hzero : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U, N.metric.IsGeodesicOn (fun s : ℝ => e (s • v))
      {s | s • v ∈ U})
    (hmetric : ∀ v w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w)
    (hgauss : ∀ v ∈ U, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    (hstar : ∀ v ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ U)
    {R a b : ℝ} (_hR : 0 < R)
    (hangle : Real.sqrt (max K 1) * R ≤ Real.pi / 4)
    {J : Set ℝ} {u : ℝ → AnnulusCoordinates} (hJ : IsOpen J)
    (hab : a ≤ b) (hsub : Icc a b ⊆ J) (hu : ContDiffOn ℝ ∞ u J)
    (humap : MapsTo u J U)
    (hboundary : ∀ s ∈ J, e (u s) = intrinsicAnnulusBoundary 1 s)
    (hnonzero : ∀ s ∈ Icc a b, u s ≠ 0)
    (hradius : ∀ s ∈ Icc a b, ‖u s‖ ≤ R)
    (hmap : ∀ s ∈ Icc a b, ∀ t ∈ Ioo (0 : ℝ) 1,
      e (t • u s) ∈ standardAnnulusDomain)
    (haorth : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (fderiv ℝ e (u a)
        ((Real.sin (Real.sqrt (max K 1) * ‖u a‖) /
          (Real.sqrt (max K 1) * ‖u a‖)) • u a))
      (intrinsicBoundaryUnitTangent N.metric 1 a) = 0)
    (hborth : N.metric.inner (intrinsicAnnulusBoundary 1 b)
      (fderiv ℝ e (u b)
        ((Real.sin (Real.sqrt (max K 1) * ‖u b‖) /
          (Real.sqrt (max K 1) * ‖u b‖)) • u b))
      (intrinsicBoundaryUnitTangent N.metric 1 b) = 0) :
    Real.cos (Real.sqrt (max K 1) * R) *
        intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * R) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  let kappa : ℝ := Real.sqrt (max K 1)
  have hkappa : 0 < kappa :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  let Y : AnnulusCoordinates → AnnulusCoordinates := fun x =>
    (Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)) • x
  let V : ℝ → AnnulusCoordinates := Y ∘ u
  let J' : Set ℝ := J ∩ u ⁻¹' ({0} : Set AnnulusCoordinates)ᶜ
  have hJ' : IsOpen J' :=
    hu.continuousOn.isOpen_inter_preimage hJ isOpen_compl_singleton
  have hsub' : Icc a b ⊆ J' := by
    intro s hs
    exact ⟨hsub hs, hnonzero s hs⟩
  have hu' : ContDiffOn ℝ ∞ u J' := hu.mono inter_subset_left
  have hV : ContDiffOn ℝ ∞ V J' := by
    intro s hs
    exact ((m64Intrinsic_contDiffAt_focusing_field hkappa.ne' hs.2).comp s
      (hu.contDiffAt (hJ.mem_nhds hs.1))).contDiffWithinAt
  have he' : ContDiffOn ℝ ∞ e U := contMDiffOn_iff_contDiffOn.mp he
  have hde : ContDiffOn ℝ ∞ (fderiv ℝ e) U := by
    intro x hx
    exact ((he'.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞)
      (by simp)).contDiffWithinAt
  let W : ℝ → AnnulusCoordinates := fun s => fderiv ℝ e (u s) (V s)
  have hW : ContDiffOn ℝ ∞ W J' :=
    (hde.comp hu' (fun s hs => humap hs.1)).clm_apply hV
  have hRpi : kappa * R < Real.pi := by
    dsimp only [kappa] at hangle ⊢
    nlinarith [Real.pi_pos]
  have hRhalf : kappa * R ≤ Real.pi / 2 := by
    dsimp only [kappa] at hangle ⊢
    nlinarith [Real.pi_pos]
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (u s)) ∧
        Real.cos (kappa * R) *
          N.metric.pullbackCoefficients e (u s) (deriv u s) (deriv u s) ≤
        N.metric.pullbackCoefficients e (u s)
          (deriv V s + coordinateChristoffel (N.metric.pullbackCoefficients e)
            (u s) (deriv u s) (V s)) (deriv u s) := by
    have hpi : Real.sqrt (max K 1) * ‖u s‖ < Real.pi :=
      (mul_le_mul_of_nonneg_left (hradius s hs) hkappa.le).trans_lt hRpi
    obtain ⟨hi, hfoc⟩ := m64Intrinsic_focusing_at_of_radial_segment N K hK
      hU hzero he hgeo hmetric hgauss (hnonzero s hs) hpi
      (hstar _ (humap (hsub hs))) (hmap s hs)
    have hnonneg : 0 ≤ N.metric.pullbackCoefficients e (u s) (deriv u s) (deriv u s) := by
      change 0 ≤ N.metric.inner (e (u s))
        (mfderiv (𝓡 2) (𝓡 2) e (u s) (deriv u s))
        (mfderiv (𝓡 2) (𝓡 2) e (u s) (deriv u s))
      by_cases hv : mfderiv (𝓡 2) (𝓡 2) e (u s) (deriv u s) = 0
      · simp only [hv, map_zero, le_refl]
      · exact (N.metric.pos _ _ hv).le
    have hcos : Real.cos (kappa * R) ≤ Real.cos (kappa * ‖u s‖) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (mul_nonneg hkappa.le (norm_nonneg _)) hRpi.le
        (mul_le_mul_of_nonneg_left (hradius s hs) hkappa.le)
    have hVderiv : deriv V s = fderiv ℝ Y (u s) (deriv u s) := by
      have hY := m64Intrinsic_contDiffAt_focusing_field hkappa.ne' (hnonzero s hs)
      exact ((hY.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
        ((hu.contDiffAt (hJ.mem_nhds (hsub hs))).differentiableAt
          (by simp)).hasDerivAt).deriv
    refine ⟨hi, ?_⟩
    have h := (mul_le_mul_of_nonneg_right hcos hnonneg).trans (hfoc (deriv u s))
    change Real.cos (kappa * R) * _ ≤ _ at h
    rw [hVderiv]
    exact h
  apply m64Intrinsic_focusing_endpoint_le_absoluteTurning N (by norm_num : (1 : ℝ) ≠ 0)
    hab hJ' hsub' hW
  · intro s hs
    have hscc : s ∈ Icc a b := Ioo_subset_Icc_self hs
    exact m64Intrinsic_pushed_boundary_focusing N hU he' hJ' hu' hV
      (fun s hs => humap hs.1) (by norm_num : (1 : ℝ) ≠ 0)
      (fun s hs => hboundary s hs.1) (hsub' hscc) (hpoint s hscc).1
        (hpoint s hscc).2
  · intro s hs
    have hscc : s ∈ Icc a b := Ioo_subset_Icc_self hs
    have hnorm := m64Intrinsic_pushed_focusing_norm_le_sin_radius N e
      (norm_pos_iff.mpr (hnonzero s hscc)) hkappa (hradius s hscc) hRhalf
      (hgauss _ (humap (hsub hscc)))
    rw [hboundary s (hsub hscc)] at hnorm
    exact hnorm
  · exact haorth
  · exact hborth




theorem m64Intrinsic_pushed_radial_field_orthogonal
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    {x : AnnulusCoordinates} (he : DifferentiableAt ℝ e x) {a : ℝ}
    (horth : N.metric.inner (e x)
      (curveVelocity (n := 2) (fun t : ℝ => e (t • x)) 1)
      (intrinsicBoundaryUnitTangent N.metric 1 a) = 0) (c : ℝ) :
    N.metric.inner (e x) (fderiv ℝ e x (c • x))
      (intrinsicBoundaryUnitTangent N.metric 1 a) = 0 := by
  have hline : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const x
  have he' : HasFDerivAt e (fderiv ℝ e x) ((1 : ℝ) • x) := by
    simpa only [one_smul] using he.hasFDerivAt
  have hvelocity : curveVelocity (n := 2) (fun t : ℝ => e (t • x)) 1 =
      fderiv ℝ e x x := by
    rw [m64Intrinsic_curveVelocity_eq_deriv]
    exact (he'.comp_hasDerivAt 1 hline).deriv
  rw [hvelocity] at horth
  simp only [map_smul, smul_apply, smul_eq_mul, horth, mul_zero]






theorem m64Intrinsic_exists_polar_focusing_map
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {p : AnnulusCoordinates} (hp : p ∈ standardAnnulusDomain)
    {R : ℝ} (hR : 0 < R)
    (hangle : Real.sqrt (max K 1) * R ≤ Real.pi / 4) :
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (U : Set AnnulusCoordinates),
      IsOpen U ∧ (0 : AnnulusCoordinates) ∈ U ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U ∧
      ∀ (a b : ℝ) (J : Set ℝ) (u : ℝ → AnnulusCoordinates),
        IsOpen J → a ≤ b → Icc a b ⊆ J → ContDiffOn ℝ ∞ u J →
        (∀ s ∈ J, e (u s) = intrinsicAnnulusBoundary 1 s) →
        (∀ s ∈ Icc a b, u s ≠ 0) →
        (∀ s ∈ Icc a b, ‖u s‖ ≤ R) →
        (∀ s ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1,
          e (t • u s) ∈ standardAnnulusDomain) →
        N.metric.inner (intrinsicAnnulusBoundary 1 a)
          (curveVelocity (n := 2) (fun t : ℝ => e (t • u a)) 1)
          (intrinsicBoundaryUnitTangent N.metric 1 a) = 0 →
        N.metric.inner (intrinsicAnnulusBoundary 1 b)
          (curveVelocity (n := 2) (fun t : ℝ => e (t • u b)) 1)
          (intrinsicBoundaryUnitTangent N.metric 1 b) = 0 →
        Real.cos (Real.sqrt (max K 1) * R) *
            intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (Real.sqrt (max K 1) * R) / Real.sqrt (max K 1)) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  obtain ⟨e, U, hU, hzero, _, hezero, he, hmetric, hgauss, hgeo, hstar, hcontains⟩ :=
    m64Intrinsic_exists_continued_radial_exponential N hp (show 0 < 2 * R by positivity)
  refine ⟨e, U, hU, hzero, hezero, he, ?_⟩
  intro a b J u hJ hab hsub hu hboundary hnonzero hradius hmap haorth hborth
  let J' : Set ℝ := J ∩ u ⁻¹' U
  have hJ' : IsOpen J' := hu.continuousOn.isOpen_inter_preimage hJ hU
  have hsub' : Icc a b ⊆ J' := by
    intro s hs
    refine ⟨hsub hs, hcontains (u s) ?_ (hmap s hs)⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (hradius s hs).trans_lt (by linarith)
  apply m64Intrinsic_varying_focusing_arc_length_le_turning N K hK hU hzero he hgeo
    hmetric hgauss hstar hR hangle hJ' hab hsub' (hu.mono inter_subset_left)
    (fun _ hs => hs.2) (fun s hs => hboundary s hs.1) hnonzero hradius
    (fun s hs t ht => hmap s hs t (Ioo_subset_Icc_self ht))
  · have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    have h := m64Intrinsic_pushed_radial_field_orthogonal N (a := a)
      ((contMDiffAt_iff_contDiffAt.mp
        (he.contMDiffAt (hU.mem_nhds (hsub' ha).2))).differentiableAt (by simp))
      (by rw [hboundary a (hsub ha)]; exact haorth)
      (Real.sin (Real.sqrt (max K 1) * ‖u a‖) / (Real.sqrt (max K 1) * ‖u a‖))
    rw [hboundary a (hsub ha)] at h
    exact h
  · have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have h := m64Intrinsic_pushed_radial_field_orthogonal N (a := b)
      ((contMDiffAt_iff_contDiffAt.mp
        (he.contMDiffAt (hU.mem_nhds (hsub' hb).2))).differentiableAt (by simp))
      (by rw [hboundary b (hsub hb)]; exact hborth)
      (Real.sin (Real.sqrt (max K 1) * ‖u b‖) / (Real.sqrt (max K 1) * ‖u b‖))
    rw [hboundary b (hsub hb)] at h
    exact h

end PoincareConjecture
