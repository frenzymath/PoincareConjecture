import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Local.Strip
import PoincareLib.Geometry.Riemannian.Coordinates.Precompact

/-!
# Continuing normal geodesics at a finite annulus endpoint

The closed coordinate annulus is compact. Energy conservation therefore
prevents the geodesic phase from escaping while its position stays in the
annulus, and the M07 compact-trajectory argument supplies the terminal
point and continuation. Completeness of the global metric is not assumed.

Morgan--Tian context: Claim 19.37, printed pp. 468-469, in the proof of Proposition
19.35. This module supplies actual normal-geodesic data or its coordinate and measure
transport.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The exact closed annulus in the frozen intrinsic definition is compact.
Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_standardAnnulus_isCompact : IsCompact standardAnnulusDomain := by
  have hclosed : IsClosed standardAnnulusDomain :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  apply (isCompact_closedBall (0 : AnnulusCoordinates) 2).of_isClosed_subset hclosed
  intro p hp
  simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2

/-- An intrinsic geodesic confined to the actual annulus extends through every finite
endpoint, and the terminal point remains in the annulus. Source/construction: Morgan--Tian
Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_annulus_geodesic_continuation
    (N : IntrinsicAnnulus) {a b : ℝ} (hab : a < b)
    {q : ℝ → AnnulusCoordinates} (hgeo : N.metric.IsGeodesicOn q (Ioo a b))
    (hmap : MapsTo q (Ioo a b) standardAnnulusDomain) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ eta : ℝ → AnnulusCoordinates,
      EqOn eta q (Ioo a b) ∧ eta b ∈ standardAnnulusDomain ∧
      N.metric.IsGeodesicOn eta (Ioo a (b + epsilon)) := by
  let p : AnnulusCoordinates := 0
  have hcoeff : N.metric.pullbackCoefficients (extChartAt (𝓡 2) p).symm =
      N.metric.euclideanCoefficients := by
    ext x v w
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe]
    change N.metric.inner x (mfderiv (𝓡 2) (𝓡 2) id x v)
      (mfderiv (𝓡 2) (𝓡 2) id x w) = N.metric.inner x v w
    rw [mfderiv_id]
    rfl
  have hfixed := hgeo.hasDerivAt_in_chart isOpen_Ioo p (fun _ _ => by simp)
  have hq (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt q (deriv q t) t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
      (hfixed t ht).1
  have hw (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (deriv q)
      (-coordinateChristoffel
        (N.metric.pullbackCoefficients (extChartAt (𝓡 2) p).symm)
        (q t) (deriv q t) (deriv q t)) t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
      (hfixed t ht).2
  obtain ⟨epsilon, hepsilon, eta, v, heq, _, hend, hflow⟩ :=
    N.metric.exists_chart_geodesic_continuation p m64Intrinsic_standardAnnulus_isCompact
      (fun _ _ => by simp) hab (fun t ht => hmap ht) hq hw
  refine ⟨epsilon, hepsilon, eta, heq, hend, ?_⟩
  have hphase (t : ℝ) (ht : t ∈ Ioo a (b + epsilon)) :
      HasDerivAt (fun s => (eta s, v s))
        (coordinateGeodesicField N.metric.euclideanCoefficients (eta t, v t)) t := by
    have h := (hflow t ht).2.1.prodMk (hflow t ht).2.2
    rw [hcoeff] at h
    exact h
  exact m64Intrinsic_isGeodesicOn_of_phase N isOpen_Ioo hphase

end PoincareMT
