import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InteriorGeodesic
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_unit_tangentNorm_of_local_metric_segment
    (G : RiemannianMetric 2 AnnulusCoordinates) {gamma : ℝ → AnnulusCoordinates}
    {u epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hgeo : G.IsGeodesicOn gamma (Ioo (u - epsilon) (u + epsilon)))
    (hmetric : ∀ s ∈ Icc (u - epsilon) (u + epsilon),
      ∀ t ∈ Icc (u - epsilon) (u + epsilon),
        G.edist (gamma s) (gamma t) = ENNReal.ofReal |s - t|) :
    G.tangentNorm (gamma u) (deriv gamma u) = 1 := by
  let d := epsilon / 3
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdu : d < epsilon := by dsimp only [d]; linarith
  have hd2 : 2 * d < epsilon := by dsimp only [d]; linarith
  let eta := fun t : ℝ => gamma (d * t + u)
  have heta : G.IsGeodesicOn eta (Ioo (-1 : ℝ) (1 + 1)) := by
    intro t ht
    apply hgeo.comp_affine d u
    constructor <;> nlinarith [ht.1, ht.2]
  have hu : u ∈ Ioo (u - epsilon) (u + epsilon) := ⟨by linarith, by linarith⟩
  have hdgamma : HasDerivAt gamma (deriv gamma u) u :=
    (contMDiffAt_iff_contDiffAt.mp (hgeo.contMDiffAt hu)).differentiableAt
      (by simp) |>.hasDerivAt
  have hdet : HasDerivAt eta (d • deriv gamma u) 0 := by
    have hdgamma' : HasDerivAt gamma (deriv gamma u) (d * 0 + u) := by
      simpa only [mul_zero, zero_add] using hdgamma
    have hh := hdgamma'.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul d).add_const u)
    simpa only [eta, Function.comp_def, id_eq, mul_zero, zero_add, mul_one] using! hh
  have hparam (t : ℝ) (ht : t ∈ Icc 0 1) : d * t + u ∈ Icc (u - epsilon) (u + epsilon) :=
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hend : G.edist (gamma u) (gamma (d + u)) = ENNReal.ofReal d := by
    have hh := hmetric u (Ioo_subset_Icc_self hu) (d + u) (by
      simpa only [mul_one] using hparam 1 ⟨zero_le_one, le_rfl⟩)
    simpa only [show u - (d + u) = -d by ring, abs_neg, abs_of_pos hd] using hh
  have hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      G.edist (eta s) (eta t) = ENNReal.ofReal |s - t| *
        G.edist (gamma u) (gamma (d + u)) := by
    intro s hs t ht
    rw [hmetric _ (hparam s hs) _ (hparam t ht), hend,
      show d * s + u - (d * t + u) = d * (s - t) by ring,
      abs_mul, abs_of_pos hd, ENNReal.ofReal_mul hd.le, mul_comm]
  have hspeed := heta.initial_tangentNorm_eq_of_edist_segment zero_lt_one
    (show eta 0 = gamma u by simp only [eta, mul_zero, zero_add])
    (show HasDerivAt (fun t => extChartAt (𝓡 2) (gamma u) (eta t))
        (d • deriv gamma u) 0 from by
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using hdet)
    hmin
  rw [hend] at hspeed
  have hreal := (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _) hd.le).mp hspeed
  change G.tangentNorm (gamma u) (d • deriv gamma u) = d at hreal
  have hscale : G.tangentNorm (gamma u) (d • deriv gamma u) =
      d * G.tangentNorm (gamma u) (deriv gamma u) := by
    simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le]
  rw [hscale] at hreal
  exact (mul_left_cancel₀ hd.ne' (hreal.trans (mul_one d).symm))




theorem m64Intrinsic_constrained_minimizer_interior_unit_speed
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma a → tau 1 = gamma b → MapsTo tau (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G tau 0 1)
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hinside : gamma u ∈ interior K) :
    G.tangentNorm (gamma u) (deriv gamma u) = 1 := by
  obtain ⟨epsilon, hepsilon, _, hmetric⟩ :=
    m64Intrinsic_constrained_minimizer_local_metric_segment G hK hlip hmin hu hinside
  obtain ⟨hgeo, _⟩ := G.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
    (γ := gamma) (a := u - epsilon) (b := u + epsilon) (c := 1) zero_le_one (by
      intro s hs t ht
      simpa only [one_mul] using hmetric s (Ioo_subset_Icc_self hs) t (Ioo_subset_Icc_self ht))
  exact m64Intrinsic_unit_tangentNorm_of_local_metric_segment G hepsilon hgeo hmetric

end PoincareConjecture
