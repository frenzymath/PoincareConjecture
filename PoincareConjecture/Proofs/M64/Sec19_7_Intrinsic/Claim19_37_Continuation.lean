import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_LocalStrip
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Precompact














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem m64Intrinsic_standardAnnulus_isCompact : IsCompact standardAnnulusDomain := by
  have hclosed : IsClosed standardAnnulusDomain :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  apply (isCompact_closedBall (0 : AnnulusCoordinates) 2).of_isClosed_subset hclosed
  intro p hp
  simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2




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

end PoincareConjecture
