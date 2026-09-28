import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Volume.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.DeckAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture

private theorem compactRound_gram_ne_zero_of_rescaled
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (c : ℝ) (hc : 0 < c) (x : M)
    (v w : TangentSpace (𝓡 3) x)
    (hgram : (rescaledMetric g c hc).inner x v v *
      (rescaledMetric g c hc).inner x w w -
      ((rescaledMetric g c hc).inner x v w) ^ 2 ≠ 0) :
    g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0 := by
  intro h
  apply hgram
  simp only [rescaledMetric_inner]
  calc
    _ = c ^ 2 * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) := by ring
    _ = 0 := by rw [h, mul_zero]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in

theorem compactRound_sectionalCurvature
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} (hround : IsRoundMetricSlice D) :
    ConstantPositiveSectionalCurvature g D := by
  obtain ⟨c, hc, hcurv⟩ := hround
  refine ⟨c, hc, fun x v w hv hw hvw => ?_⟩
  simp [LeviCivitaData.sectionalCurvature, hcurv, hv, hw, hvw]

theorem compactRoundAncientQuotient
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (Set.univ : Set M))
    (hround : ConstantPositiveSectionalCurvature (K.flow.metric 0)
      (K.flow.connection 0)) :
    Nonempty (RoundAncientQuotientCertificate K) := by
  classical
  let : CompactSpace M := ⟨hcompact⟩
  obtain ⟨c, hc, hsec⟩ := hround
  let g := rescaledMetric (K.flow.metric 0) c hc
  let D := rescaledMetric_connection (K.flow.metric 0) (K.flow.connection 0) c hc
  have hg : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0 →
      g.leviCivitaData.sectionalCurvature x v w = 1 := by
    intro x v w hgram
    have heq : g.leviCivitaData.sectionalCurvature x v w =
        D.sectionalCurvature x v w := by
      simp only [LeviCivitaData.sectionalCurvature, g.leviCivitaData.horizon_curvatureTensor_eq D]
      rfl
    rw [heq, rescaledMetric_sectionalCurvature,
      (K.flow.connection 0).sectionalCurvature_eq_of_orthonormal x c (hsec x) v w
        (compactRound_gram_ne_zero_of_rescaled _ c hc x v w hgram),
      inv_mul_cancel₀ hc.ne']
  obtain ⟨q, hqsmooth, hqsurj, hqlocal, hqmetric⟩ := exists_spherical_covering g hg
  let : Finite (orthogonalDeckGroup q) := orthogonalDeckGroup_finite q hqlocal
  let Γ := ULift.{u} (orthogonalDeckGroup q)
  let : Fintype Γ := Fintype.ofFinite Γ
  let gs := rescaledMetric (roundSphereMetric 3) c⁻¹ (inv_pos.mpr hc)
  let Ds := rescaledMetric_connection (roundSphereMetric 3)
    (roundSphereMetric 3).leviCivitaData c⁻¹ (inv_pos.mpr hc)
  have hsround : ConstantPositiveSectionalCurvature gs Ds := by
    refine ⟨c, hc, fun x v w hv hw hvw => ?_⟩
    have hgram : gs.inner x v v * gs.inner x w w - (gs.inner x v w) ^ 2 ≠ 0 := by
      rw [hv, hw, hvw]
      norm_num
    rw [rescaledMetric_sectionalCurvature,
      roundSphereMetric_unit_sectionalCurvature x v w
        (compactRound_gram_ne_zero_of_rescaled _ c⁻¹ (inv_pos.mpr hc) x v w hgram),
      inv_inv, mul_one]
  refine ⟨{
    quotient_carrier := M
    quotient_topology := inferInstance
    quotient_charted := inferInstance
    quotient_manifold := inferInstance
    round_metric := gs
    round_connection := Ds
    round_model := hsround
    quotient_metric := K.flow.metric 0
    quotient_connection := K.flow.connection 0
    quotient_diffeomorph := Diffeomorph.refl (𝓡 3) M ∞
    group := Γ
    group_finite := inferInstance
    group_structure := inferInstance
    action := fun a x => a.down • x
    action_identity := fun x => one_smul (orthogonalDeckGroup q) x
    action_comp := fun a b x => mul_smul a.down b.down x
    action_free := ?_
    action_smooth := fun a => orthogonalDeckGroup_contMDiff q a.down
    action_distance_preserving := fun a x y => orthogonalDeckGroup_dist_smul q a.down x y
    action_orientation_preserving := fun a => ⟨sphereMotionMatrix a.down.val,
      orthogonalDeckGroup_det_one q hqlocal a.down,
      fun x => orthogonalDeckGroup_action_representation q a.down x⟩
    quotient_map := q
    quotient_map_surjective := hqsurj
    quotient_map_smooth := hqsmooth
    quotient_metric_transport := ?_
    flow_metric_transport := ?_
    quotient_fiber := ?_
  }⟩
  · intro a x ha
    apply ULift.ext
    exact orthogonalDeckGroup_free q hqlocal a.down x ha
  · intro x v w
    change _ = c⁻¹ * (roundSphereMetric 3).inner x v w
    rw [← hqmetric x v w, rescaledMetric_inner, ← mul_assoc, inv_mul_cancel₀ hc.ne',
      one_mul]
  · intro x v w
    simp only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
  · intro x y
    change q x = q y ↔ ∃ a : Γ, a.down • x = y
    rw [orthogonalDeckGroup_orbit_iff g q hqlocal hqmetric]
    exact ⟨fun ⟨a, ha⟩ => ⟨ULift.up a, ha⟩, fun ⟨a, ha⟩ => ⟨a.down, ha⟩⟩

end PoincareConjecture
