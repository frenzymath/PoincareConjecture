import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.InitialData
import PoincareLib.Geometry.Riemannian.Distance.ExponentialRays
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.OrbitConvexity
import PoincareLib.Geometry.CurveShortening.Comparison.Geometry
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Extending the actual outgoing geodesic to a boundary contact

Compact position confinement and conserved energy allow coordinate ODE
continuation. Time reversal gives an extension through a finite left
endpoint, and continuity identifies its endpoint with the original curve.
Source: MT Claim 19.40, pp. 470-471; minimal-contact-regularity derivation.
No completeness of the ambient plane metric is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- A geodesic confined to any actual compact planar region extends past its finite right
endpoint, with terminal position in that region. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/derivations/2026-09-27-minimal-contact-regularity.md`, Sections 3 and
10. -/
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

/-- Compact confinement extends a geodesic through its left endpoint. The original right
continuity identifies the extension there, so the agreement includes the endpoint and
supplies a genuine right derivative. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/derivations/2026-09-27-minimal-contact-regularity.md`, Sections 3 and
10. -/
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

/-- The actual compact outgoing geodesic has a right derivative at its continuous boundary
endpoint. This supplies the derivative input of the local constrained-minimizer tangency
theorem. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/derivations/2026-09-27-minimal-contact-regularity.md`, Sections 3 and
10. -/
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

/-- A distinct later point forces the actual outgoing endpoint derivative to be nonzero. The
extension includes the endpoint, so M07's constant-speed argument applies on a genuine
closed subinterval through that point. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/derivations/2026-09-27-minimal-contact-regularity.md`, Sections 3 and
10. -/
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

end PoincareMT
