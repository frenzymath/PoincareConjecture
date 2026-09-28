import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SelectedTube

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem SeparatedCircleSource.identity_source_subset
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R)
    {i : D.decomposition.Index} {L d : ℝ}
    (T : ComponentIdentityAnnuliData (e := e) (R := R) D.decomposition i L d)
    (hi : D.decomposition.pieces i = C₀)
    (hmi : D.decomposition.pieces (D.decomposition.mate i) = D.shift '' C₁)
    (j : Fin 2) :
    T.source j ⊆ if T.label j = 0 then D.first.space else D.shift '' D.second.space := by
  have hd := T.depth_pos
  have hwidth := T.width_small
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  let : ConnectedSpace (Icc (-d) d) := isConnected_iff_connectedSpace.mp
    (isConnected_Icc (show -d ≤ d by linarith))
  obtain ⟨E,_⟩ := exists_annulus_homeomorph (show 0 < L by linarith) hd.le hwidth
  let : ConnectedSpace (squareAnnulus L d) := E.connectedSpace_iff.mp inferInstance
  have hconn : IsConnected (T.source j) := isConnected_iff_connectedSpace.mpr
    ((T.chart j).connectedSpace_iff.mp inferInstance)
  have hsub : T.source j ⊆ D.first.space ∪ D.shift '' D.second.space :=
    (T.source_interior j).trans (interior_subset.trans D.source_space.subset)
  have hcases := isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected
    D.first.space (D.shift '' D.second.space)
    (D.first.isCompact_space_of_finite D.first_finite).isClosed
    ((D.second.isCompact_space_of_finite D.second_finite).image D.shift.continuous).isClosed
    hsub (by rw [D.disjoint.inter_eq,inter_empty])
  let p : squareAnnulus L d := ⟨annulusMap L (by linarith) ((0 : AddCircle (4 * L)), 0),
    _root_.Dehn.annulus_period_point_mem hd hwidth 0 ⟨0,by constructor <;> linarith⟩⟩
  have hpd : depth L (p : P2) = 0 := depth_annulusMap (by linarith) (by simp; linarith) _
  have hpm := (T.middle j p).mpr hpd
  rw [hi,hmi] at hpm
  by_cases hj : T.label j = 0
  · simp only [hj,if_true] at hpm ⊢
    exact hcases.resolve_right (fun h => disjoint_left.mp D.disjoint
      (interior_subset (D.first_selected hpm)) (h (T.chart j p).property))
  · simp only [hj,if_false] at hpm ⊢
    exact hcases.resolve_left (fun h => disjoint_left.mp D.disjoint (h (T.chart j p).property)
      (image_mono (D.second_selected.trans interior_subset) hpm))

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
