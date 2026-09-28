import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.ConvexExterior
import Mathlib.Topology.Connected.Basic











set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Plane



theorem exists_unbounded_compl_component {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hdim : 1 < Module.rank ℝ E)
    {C : Set E} (hC : Bornology.IsBounded C) :
    ∃ x ∉ C, ¬ Bornology.IsBounded (connectedComponentIn Cᶜ x) ∧
      ∀ y ∉ C, connectedComponentIn Cᶜ y ≠ connectedComponentIn Cᶜ x →
        Bornology.IsBounded (connectedComponentIn Cᶜ y) := by
  classical
  let : Nontrivial E := rank_pos_iff_nontrivial.mp (zero_lt_one.trans hdim)
  obtain ⟨r, hCr⟩ := hC.subset_closedBall (0 : E)
  have hA := isPathConnected_compl_closedBall_of_one_lt_rank hdim (0 : E) r
  have hAnb : ¬ Bornology.IsBounded (closedBall (0 : E) r)ᶜ := by
    intro hbounded
    apply NormedSpace.unbounded_univ ℝ E
    simpa only [union_compl_self] using
      (Metric.isBounded_closedBall (x := (0 : E)) (r := r)).union hbounded
  have hAC : (closedBall (0 : E) r)ᶜ ⊆ Cᶜ := compl_subset_compl.mpr hCr
  obtain ⟨x, hx⟩ := hA.nonempty
  have hAK : (closedBall (0 : E) r)ᶜ ⊆ connectedComponentIn Cᶜ x :=
    hA.isConnected.isPreconnected.subset_connectedComponentIn hx hAC
  refine ⟨x, hAC hx, fun hb => hAnb (hb.subset hAK), ?_⟩
  intro y _ hne
  apply (Metric.isBounded_closedBall (x := (0 : E)) (r := r)).subset
  intro z hz
  by_contra hzB
  exact hne ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq (hAK hzB)).symm)

end Poincare.Manifold.Schoenflies.Plane
