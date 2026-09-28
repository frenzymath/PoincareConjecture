import PoincareConjecture.Proofs.M35.TerminalBlowup.ScalarReciprocalGradient
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem scalar_variation_le_path_length
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

theorem component_maximum_scalar_patch
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hreg : ContMDiff (𝓡 3) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature)
    {B H : ℝ} (hB : 0 < B) (hH : 0 < H) (x : M)
    (hcenter : D.scalarCurvature x = H)
    (hupper : ∀ z ∈ connectedComponent x, D.scalarCurvature z ≤ H)
    (hgrad : ∀ z ∈ connectedComponent x, 3 * H / 4 ≤ D.scalarCurvature z →
      ∀ v : TangentSpace (𝓡 3) z, g.inner z v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature z v| ≤
          B * D.scalarCurvature z ^ (3 / 2 : ℝ)) :
    ∀ y ∈ g.ball x ((Real.sqrt H)⁻¹ / (8 * B)),
      3 * H / 4 ≤ D.scalarCurvature y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  by_contra hbad
  have hlow : D.scalarCurvature y < 3 * H / 4 := lt_of_not_ge hbad
  obtain ⟨gamma, hzero, hone, hgamma, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  let f (s : ℝ) := D.scalarCurvature (gamma s)
  have hfzero : f 0 = H := by simp only [f, hzero, hcenter]
  have hcont : ContinuousOn f (Icc 0 1) :=
    hreg.continuous.comp_continuousOn hgamma.continuousOn
  have hcomponent (s : ℝ) (hs : s ∈ Icc 0 1) : gamma s ∈ connectedComponent x :=
    (isPreconnected_Icc.image gamma hgamma.continuousOn).subset_connectedComponent
      ⟨0, ⟨le_rfl, zero_le_one⟩, hzero⟩ ⟨s, hs, rfl⟩
  have hlowerClosed : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' Iic (3 * H / 4)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨b, hb, hfirst⟩ :=
    (isCompact_Icc.of_isClosed_subset hlowerClosed inter_subset_left).exists_isLeast
      ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by
        change f 1 ≤ 3 * H / 4
        simpa only [f, hone] using hlow.le⟩⟩
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne hb.1.1
    intro heq
    have h : f b ≤ 3 * H / 4 := hb.2
    rw [← heq, hfzero] at h
    linarith
  have hbvalue : f b = 3 * H / 4 := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' hbpos.le
      (hcont.mono (Icc_subset_Icc le_rfl hb.1.2))
      ⟨hb.2, by rw [hfzero]; linarith⟩
    have hbs : b ≤ s := hfirst ⟨⟨hs.1, hs.2.trans hb.1.2⟩, hfs.le⟩
    simpa only [le_antisymm hbs hs.2] using hfs
  have hband (s : ℝ) (hs : s ∈ Icc 0 b) :
      3 * H / 4 ≤ f s ∧ f s ≤ H := by
    constructor
    · by_cases hsb : s = b
      · simp only [hsb, hbvalue, le_refl]
      have hsb' : s < b := lt_of_le_of_ne hs.2 hsb
      by_contra hlo
      exact not_le_of_gt hsb'
        (hfirst ⟨⟨hs.1, hs.2.trans hb.1.2⟩, (lt_of_not_ge hlo).le⟩)
    · exact hupper (gamma s) (hcomponent s ⟨hs.1, hs.2.trans hb.1.2⟩)
  have hdiff (s : ℝ) (hs : s ∈ Icc 0 b)
      (v : TangentSpace (𝓡 3) (gamma s)) (hv : g.inner (gamma s) v v = 1) :
      |mvfderiv (𝓡 3) D.scalarCurvature (gamma s) v| ≤ B * H ^ (3 / 2 : ℝ) := by
    obtain ⟨hlo, hhi⟩ := hband s hs
    have hfpos : 0 < f s := (by positivity : 0 < 3 * H / 4).trans_le hlo
    exact (hgrad (gamma s) (hcomponent s ⟨hs.1, hs.2.trans hb.1.2⟩) hlo v hv).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfpos.le hhi (by norm_num)) hB.le)
  have hK : 0 < B * H ^ (3 / 2 : ℝ) := mul_pos hB (Real.rpow_pos_of_pos hH _)
  have hdist := scalar_variation_le_path_length g D hreg hbpos.le hK.le
    (hgamma.mono (Icc_subset_Icc le_rfl hb.1.2)) hdiff
  change edist (f 0) (f b) ≤ _ at hdist
  rw [hfzero, hbvalue] at hdist
  have hmono : g.pathELength gamma 0 b ≤ g.pathELength gamma 0 1 :=
    Manifold.pathELength_mono le_rfl hb.1.2
  have hstrict := ENNReal.mul_lt_mul_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr hK)) ENNReal.ofReal_ne_top hlength
  have heq : ENNReal.ofReal (B * H ^ (3 / 2 : ℝ)) *
      ENNReal.ofReal ((Real.sqrt H)⁻¹ / (8 * B)) = ENNReal.ofReal (H / 8) := by
    rw [← ENNReal.ofReal_mul hK.le]
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add hH, Real.rpow_one, ← Real.sqrt_eq_rpow]
    field_simp [hB.ne', (Real.sqrt_pos.mpr hH).ne']
  have hsmall := (hdist.trans (mul_le_mul_right hmono _)).trans_lt (hstrict.trans_eq heq)
  rw [edist_dist, Real.dist_eq, show H - 3 * H / 4 = H / 4 by ring,
    abs_of_pos (by positivity : 0 < H / 4)] at hsmall
  have hsmallReal := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < H / 8)).mp hsmall
  linarith

end PoincareConjecture.M47
