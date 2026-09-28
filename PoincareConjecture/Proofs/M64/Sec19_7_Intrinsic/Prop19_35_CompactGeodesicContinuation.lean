import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.InitialData
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.OrbitConvexity
import PoincareConjecture.Definitions.Ch19.AnnulusComparison
import Mathlib.Analysis.Calculus.TangentCone.Real











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_compact_geodesic_right_extension
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {a b : ℝ} (hab : a < b) {q : ℝ → AnnulusCoordinates}
    (hgeo : G.IsGeodesicOn q (Ioo a b)) (hmap : MapsTo q (Ioo a b) K) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ eta : ℝ → AnnulusCoordinates,
      EqOn eta q (Ioo a b) ∧ eta b ∈ K ∧ G.IsGeodesicOn eta (Ioo a (b + epsilon)) := by
  let p : AnnulusCoordinates := 0
  have hfixed := hgeo.hasDerivAt_in_chart isOpen_Ioo p (fun _ _ => by simp)
  have hq (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt q (deriv q t) t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
      (hfixed t ht).1
  have hw (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (deriv q)
      (-coordinateChristoffel (G.pullbackCoefficients (extChartAt (𝓡 2) p).symm)
        (q t) (deriv q t) (deriv q t)) t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
      (hfixed t ht).2
  obtain ⟨epsilon, hepsilon, eta, v, heq, _, hend, hflow⟩ :=
    G.exists_chart_geodesic_continuation p hK (fun _ _ => by simp) hab
      (fun t ht => hmap ht) hq hw
  refine ⟨epsilon, hepsilon, eta, heq, hend, ?_⟩
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq] using!
    G.isGeodesicOn_chart_curve p isOpen_Ioo hflow






theorem m64Intrinsic_compact_geodesic_left_extension
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {a b : ℝ} (hab : a < b) {q : ℝ → AnnulusCoordinates}
    (hgeo : G.IsGeodesicOn q (Ioo a b)) (hmap : MapsTo q (Ioo a b) K)
    (hc : ContinuousWithinAt q (Ici a) a) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ eta : ℝ → AnnulusCoordinates,
      EqOn eta q (Ico a b) ∧ G.IsGeodesicOn eta (Ioo (a - epsilon) b) := by
  have hrev : G.IsGeodesicOn (fun t => q (-t)) (Ioo (-b) (-a)) := by
    have hh := hgeo.comp_affine (-1) 0
    simp only [neg_one_mul, add_zero] at hh
    intro t ht
    exact hh t ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨epsilon, hepsilon, eta, heq, _, heta⟩ :=
    m64Intrinsic_compact_geodesic_right_extension G hK (neg_lt_neg hab) hrev
      (fun t ht => hmap ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  let zeta := fun t => eta (-t)
  have hzeta : G.IsGeodesicOn zeta (Ioo (a - epsilon) b) := by
    have hh := heta.comp_affine (-1) 0
    simp only [neg_one_mul, add_zero] at hh
    intro t ht
    exact hh t ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hza : ContinuousAt zeta a :=
    (hzeta.contMDiffAt (show a ∈ Ioo (a - epsilon) b from ⟨by linarith, hab⟩)).continuousAt
  have hnear : zeta =ᶠ[𝓝[>] a] q := by
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    have h := heq (show -t ∈ Ioo (-b) (-a) from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    simpa only [zeta, neg_neg] using h
  have hpoint : zeta a = q a :=
    tendsto_nhds_unique ((hza.tendsto.mono_left nhdsWithin_le_nhds).congr' hnear)
      (hc.mono Ioi_subset_Ici_self)
  refine ⟨epsilon, hepsilon, zeta, ?_, hzeta⟩
  intro t ht
  rcases ht.1.eq_or_lt with h | h
  · simpa only [← h] using hpoint
  · have hh := heq (show -t ∈ Ioo (-b) (-a) from ⟨by linarith [ht.2], by linarith⟩)
    simpa only [zeta, neg_neg] using hh






theorem m64Intrinsic_compact_geodesic_has_right_derivative
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {a b : ℝ} (hab : a < b) {q : ℝ → AnnulusCoordinates}
    (hgeo : G.IsGeodesicOn q (Ioo a b)) (hmap : MapsTo q (Ioo a b) K)
    (hc : ContinuousWithinAt q (Ici a) a) :
    ∃ v : AnnulusCoordinates, HasDerivWithinAt q v (Ioi a) a := by
  obtain ⟨epsilon, hepsilon, eta, heq, heta⟩ :=
    m64Intrinsic_compact_geodesic_left_extension G hK hab hgeo hmap hc
  have hd : HasDerivAt eta (deriv eta a) a :=
    (contMDiffAt_iff_contDiffAt.mp (heta.contMDiffAt
      (show a ∈ Ioo (a - epsilon) b from ⟨by linarith, hab⟩))).differentiableAt
        (by simp) |>.hasDerivAt
  refine ⟨deriv eta a, hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (heq ⟨ht.1.le, ht.2⟩).symm
  · exact (heq ⟨le_rfl, hab⟩).symm






theorem m64Intrinsic_compact_geodesic_right_derivative_ne_zero
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {a b : ℝ} (hab : a < b) {q : ℝ → AnnulusCoordinates}
    (hgeo : G.IsGeodesicOn q (Ioo a b)) (hmap : MapsTo q (Ioo a b) K)
    (hc : ContinuousWithinAt q (Ici a) a) {c : ℝ} (hcab : c ∈ Ioo a b)
    (hne : q a ≠ q c) {v : AnnulusCoordinates}
    (hv : HasDerivWithinAt q v (Ioi a) a) : v ≠ 0 := by
  obtain ⟨epsilon, hepsilon, eta, heq, heta⟩ :=
    m64Intrinsic_compact_geodesic_left_extension G hK hab hgeo hmap hc
  have hd : HasDerivAt eta (deriv eta a) a :=
    (contMDiffAt_iff_contDiffAt.mp (heta.contMDiffAt
      (show a ∈ Ioo (a - epsilon) b from ⟨by linarith, hab⟩))).differentiableAt
        (by simp) |>.hasDerivAt
  have hdq : HasDerivWithinAt q (deriv eta a) (Ioi a) a := by
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact (heq ⟨ht.1.le, ht.2⟩).symm
    · exact (heq ⟨le_rfl, hab⟩).symm
  have hveq : v = deriv eta a :=
    (hv.derivWithin (uniqueDiffWithinAt_Ioi a)).symm.trans
      (hdq.derivWithin (uniqueDiffWithinAt_Ioi a))
  rw [hveq]
  apply heta.deriv_ne_zero_of_endpoints_ne isOpen_Ioo hcab.1.le
    (show Icc a c ⊆ Ioo (a - epsilon) b from fun t ht =>
      ⟨by linarith [ht.1], ht.2.trans_lt hcab.2⟩)
    (show eta a ≠ eta c from by rw [heq ⟨le_rfl, hab⟩, heq ⟨hcab.1.le, hcab.2⟩]; exact hne)
  exact ⟨le_rfl, hcab.1.le⟩

end PoincareConjecture
