import PoincareConjecture.Proofs.M35.TerminalBlowup.ScalarReciprocalGradient
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem scalar_edist_le_length
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hreg : ContMDiff (𝓡 3) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature)
    {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    {gamma : ℝ → M} (hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1 gamma (Icc a b))
    (hgrad : ∀ s ∈ Icc a b, ∀ v : TangentSpace (𝓡 3) (gamma s),
      g.inner (gamma s) v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature (gamma s) v| ≤ K) :
    edist (D.scalarCurvature (gamma a)) (D.scalarCurvature (gamma b)) ≤
      ENNReal.ofReal K * g.pathELength gamma a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let r : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap a b
  have hrange : MapsTo r (Icc 0 1) (Icc a b) := by
    rw [mapsTo_iff_image_subset, show (r : ℝ → ℝ) = AffineMap.lineMap a b from rfl,
      ← segment_eq_image_lineMap, segment_eq_Icc hab]
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1 (gamma ∘ r) (Icc 0 1) :=
    hgamma.comp r.contDiff.contMDiff.contMDiffOn hrange
  have hlength : g.pathELength (gamma ∘ r) 0 1 = g.pathELength gamma a b := by
    change Manifold.pathELength (𝓡 3) (gamma ∘ r) 0 1 =
      Manifold.pathELength (𝓡 3) gamma a b
    have h := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3)
      (γ := gamma) (f := r) zero_le_one
      ((AffineMap.lineMap_mono hab).monotoneOn (Icc 0 1)) r.differentiableOn
      (by simpa [r, ContinuousAffineMap.coe_lineMap_eq] using
        hgamma.mdifferentiableOn one_ne_zero)
    simpa [r, ContinuousAffineMap.coe_lineMap_eq] using h
  have hnorm (z : M) (hz : z ∈ gamma '' Icc a b) :
      ‖mfderiv (𝓡 3) (𝓘(ℝ, ℝ)) D.scalarCurvature z‖ ≤ K := by
    obtain ⟨s, hs, rfl⟩ := hz
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro v
    have h := D.scalar_directional_bound_of_unit_bound (gamma s) (hgrad s hs) v
    have hv : g.tangentNorm (gamma s) v = ‖v‖ := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    have hn : ‖mfderiv (𝓡 3) (𝓘(ℝ, ℝ)) D.scalarCurvature (gamma s) v‖ =
        |mvfderiv (𝓡 3) D.scalarCurvature (gamma s) v| := by
      change ‖mvfderiv (𝓡 3) D.scalarCurvature (gamma s) v‖ = _
      exact Real.norm_eq_abs _
    rw [hn]
    simpa only [hv] using h
  let K' : ℝ≥0 := ⟨K, hK⟩
  have hKcoe : (K' : ℝ≥0∞) = ENNReal.ofReal K := ENNReal.coe_nnreal_eq K'
  have hbound (z : M) (hz : z ∈ gamma '' Icc a b) :
      ‖mfderiv (𝓡 3) (𝓘(ℝ, ℝ)) D.scalarCurvature z‖ₑ ≤ (K' : ℝ≥0∞) := by
    rw [hKcoe, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hnorm z hz)
  have h := Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (fun z (_hz : z ∈ gamma '' Icc a b) => (hreg z).of_le (by simp)) hbound hcomp
    (fun s hs => ⟨r s, hrange hs, rfl⟩)
  change edist (D.scalarCurvature (gamma (r 0))) (D.scalarCurvature (gamma (r 1))) ≤
    (K' : ℝ≥0∞) * g.pathELength (gamma ∘ r) 0 1 at h
  rw [hlength, hKcoe] at h
  simpa only [r, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using h

theorem scalar_le_two_inv_sq_on_ball
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hreg : ContMDiff (𝓡 3) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature)
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : M)
    (hcenter : D.scalarCurvature x ≤ r⁻¹ ^ 2)
    (hgrad : ∀ z ∈ g.ball x (r / (8 * B)), r⁻¹ ^ 2 ≤ D.scalarCurvature z →
      ∀ v : TangentSpace (𝓡 3) z, g.inner z v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature z v| ≤
          B * D.scalarCurvature z ^ (3 / 2 : ℝ)) :
    ∀ y ∈ g.ball x (r / (8 * B)), D.scalarCurvature y ≤ 2 * r⁻¹ ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  by_contra hbad
  have hhigh : 2 * r⁻¹ ^ 2 < D.scalarCurvature y := lt_of_not_ge hbad
  have hq : 0 < r⁻¹ := inv_pos.mpr hr
  have hq2 : 0 < r⁻¹ ^ 2 := sq_pos_of_pos hq
  obtain ⟨gamma, hzero, hone, hgamma, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  let f (s : ℝ) := D.scalarCurvature (gamma s)
  have hcont : ContinuousOn f (Icc 0 1) :=
    hreg.continuous.comp_continuousOn hgamma.continuousOn
  have hball (s : ℝ) (hs : s ∈ Icc 0 1) : gamma s ∈ g.ball x (r / (8 * B)) := by
    exact ((Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc le_rfl hs.2)) hzero rfl hs.1).trans
        (Manifold.pathELength_mono le_rfl hs.2)).trans_lt hlength
  have hupperClosed : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' Ici (2 * r⁻¹ ^ 2)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  obtain ⟨b, hb, hfirst⟩ :=
    (isCompact_Icc.of_isClosed_subset hupperClosed inter_subset_left).exists_isLeast
      ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by
        change 2 * r⁻¹ ^ 2 ≤ f 1
        simpa only [f, hone] using hhigh.le⟩⟩
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne hb.1.1
    intro heq
    have h : 2 * r⁻¹ ^ 2 ≤ f b := hb.2
    rw [← heq, show f 0 = D.scalarCurvature x by simp only [f, hzero]] at h
    linarith
  have hbvalue : f b = 2 * r⁻¹ ^ 2 := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hbpos.le
      (hcont.mono (Icc_subset_Icc le_rfl hb.1.2))
      ⟨by simpa only [f, hzero] using hcenter.trans (by linarith : r⁻¹ ^ 2 ≤ 2 * r⁻¹ ^ 2),
        hb.2⟩
    have hbs : b ≤ s := hfirst ⟨⟨hs.1, hs.2.trans hb.1.2⟩, hfs.ge⟩
    simpa only [le_antisymm hbs hs.2] using hfs
  have hlowerClosed : IsClosed (Icc (0 : ℝ) b ∩ f ⁻¹' Iic (r⁻¹ ^ 2)) :=
    (hcont.mono (Icc_subset_Icc le_rfl hb.1.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  obtain ⟨a, ha, hlast⟩ :=
    (isCompact_Icc.of_isClosed_subset hlowerClosed inter_subset_left).exists_isGreatest
      ⟨0, ⟨⟨le_rfl, hbpos.le⟩, by
        change f 0 ≤ r⁻¹ ^ 2
        simpa only [f, hzero] using hcenter⟩⟩
  have hab : a < b := by
    apply lt_of_le_of_ne ha.1.2
    intro heq
    have h : f a ≤ r⁻¹ ^ 2 := ha.2
    rw [heq, hbvalue] at h
    linarith
  have havalue : f a = r⁻¹ ^ 2 := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab.le
      (hcont.mono (Icc_subset_Icc ha.1.1 hb.1.2))
      ⟨ha.2, by rw [hbvalue]; linarith⟩
    have hsa : s ≤ a := hlast ⟨⟨ha.1.1.trans hs.1, hs.2⟩, hfs.le⟩
    simpa only [le_antisymm hsa hs.1] using hfs
  have hband (s : ℝ) (hs : s ∈ Icc a b) : r⁻¹ ^ 2 ≤ f s ∧ f s ≤ 2 * r⁻¹ ^ 2 := by
    constructor
    · by_cases hsa : s = a
      · simp only [hsa, havalue, le_refl]
      have has : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
      by_contra hlo
      exact not_le_of_gt has (hlast ⟨⟨ha.1.1.trans hs.1, hs.2⟩, (lt_of_not_ge hlo).le⟩)
    · by_cases hsb : s = b
      · simp only [hsb, hbvalue, le_refl]
      have hsb' : s < b := lt_of_le_of_ne hs.2 hsb
      by_contra hhi
      exact not_le_of_gt hsb'
        (hfirst ⟨⟨ha.1.1.trans hs.1, hs.2.trans hb.1.2⟩, (lt_of_not_ge hhi).le⟩)
  have hdiff (s : ℝ) (hs : s ∈ Icc a b)
      (v : TangentSpace (𝓡 3) (gamma s)) (hv : g.inner (gamma s) v v = 1) :
      |mvfderiv (𝓡 3) D.scalarCurvature (gamma s) v| ≤ 4 * B * r⁻¹ ^ 3 := by
    obtain ⟨hlo, hhi⟩ := hband s hs
    have hfpos : 0 < f s := hq2.trans_le hlo
    have hsqrt : Real.sqrt (f s) ≤ 2 * r⁻¹ :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith [sq_nonneg r⁻¹]⟩
    have hp : f s ^ (3 / 2 : ℝ) ≤ 4 * r⁻¹ ^ 3 := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
        Real.rpow_add hfpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have h := mul_le_mul hhi hsqrt (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * r⁻¹ ^ 2)
      nlinarith
    have h := (hgrad (gamma s) (hball s ⟨ha.1.1.trans hs.1, hs.2.trans hb.1.2⟩)
      hlo v hv).trans (mul_le_mul_of_nonneg_left hp hB.le)
    nlinarith
  have hdist := scalar_edist_le_length g D hreg hab.le (by positivity : 0 ≤ 4 * B * r⁻¹ ^ 3)
    (hgamma.mono (Icc_subset_Icc ha.1.1 hb.1.2)) hdiff
  change edist (f a) (f b) ≤ _ at hdist
  rw [havalue, hbvalue] at hdist
  have hmono : g.pathELength gamma a b ≤ g.pathELength gamma 0 1 :=
    Manifold.pathELength_mono ha.1.1 hb.1.2
  have hstrict := ENNReal.mul_lt_mul_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < 4 * B * r⁻¹ ^ 3)))
    ENNReal.ofReal_ne_top hlength
  have heq : ENNReal.ofReal (4 * B * r⁻¹ ^ 3) * ENNReal.ofReal (r / (8 * B)) =
      ENNReal.ofReal (r⁻¹ ^ 2 / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * B * r⁻¹ ^ 3)]
    congr 1
    field_simp
    ring
  have hsmall := (hdist.trans (mul_le_mul_right hmono _)).trans_lt (hstrict.trans_eq heq)
  rw [edist_dist, Real.dist_eq, show r⁻¹ ^ 2 - 2 * r⁻¹ ^ 2 = -(r⁻¹ ^ 2) by ring,
    abs_neg, abs_of_pos hq2] at hsmall
  have hsmallReal := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r⁻¹ ^ 2 / 2)).mp hsmall
  linarith

end PoincareConjecture.Proofs.M46
