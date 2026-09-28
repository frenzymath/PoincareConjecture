import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FinitePLBallAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.WholeCapRimContact

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem finitePL_disk_boundary_isConnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D r : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D r) : IsConnected r := by
  let c : (ℝ × ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨d,_,hdr⟩ := hD.exists_cube_chart c
  let e := d.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hdr
  exact e.isConnected_of_convex_frontier (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp)

theorem isConnected_two_cap_boundary_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S U : Set E} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B S)
    (A a : Bool → Set E) (hA : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (A b) (a b))
    (hdis : Disjoint (A false) (A true)) (hU : IsClosed U)
    (hcontact : ∀ b, U ∩ A b = a b) (hcover : (U ∪ A false) ∪ A true = S) :
    IsConnected U := by
  have hc (b : Bool) := finitePL_disk_boundary_isConnected (hA b)
  obtain ⟨H₀,_⟩ := Topology.exists_components_homeomorph_closed_attachment hU
    (hA false).isCompact.isClosed (hA false).isConnected
      ((hcontact false).symm ▸ hc false)
  have hinter : (U ∪ A false) ∩ A true = a true := by
    rw [union_inter_distrib_right,hdis.inter_eq,union_empty,hcontact]
  obtain ⟨H₁,_⟩ := Topology.exists_components_homeomorph_closed_attachment
    (hU.union (hA false).isCompact.isClosed)
    (hA true).isCompact.isClosed (hA true).isConnected (hinter.symm ▸ hc true)
  have hfilled : ConnectedSpace ((U ∪ A false) ∪ A true : Set E) := by
    rw [hcover]
    exact isConnected_iff_connectedSpace.mp hB.isConnected_boundary_three
  let := hfilled
  have hclasses (x y : U) : ConnectedComponents.mk x = ConnectedComponents.mk y :=
    H₀.injective (H₁.injective (Subsingleton.elim _ _))
  let : PreconnectedSpace U := preconnectedSpace_iff_connectedComponent.mpr (fun x => by
    apply eq_univ_of_forall
    intro y
    exact ConnectedComponents.coe_eq_coe'.mp (hclasses y x))
  obtain ⟨x,hx⟩ := (hc false).nonempty
  let : Nonempty U := ⟨⟨x,((hcontact false).symm.subset hx).1⟩⟩
  let : ConnectedSpace U := { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  exact isConnected_iff_connectedSpace.mpr (show ConnectedSpace U from inferInstance)

end PoincareConjecture.M76.PrismBelt
