import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskCircleSelection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.SelectedStep
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment










set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_paired_innermost_disk_of_region_contact
    {X : Type*} {J K B : Set P2} {f g : P2 → X}
    (hJ : Convex ℝ J)
    (C : SurfaceIntersectionComponents J K f g B)
    (D : SurfaceIntersectionComponents K J g f (frontier J))
    (hrims : ∀ x ∈ J, ∀ y ∈ K, f x = g y →
      (x ∈ frontier J ↔ y ∈ B))
    (hgood : ∃ i, ∃ (n : ℕ)
      (P : Polygon P2 (n+3)), Function.Injective P ∧ P.HasSimplicialEdges ∧
      P.boundary ℝ = C.pieces i ∧ closure P.inside ⊆ interior K \ B) :
    ∃ i j, ∃ (n m : ℕ) (P : Polygon P2 (n+3)) (Q : Polygon P2 (m+3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      P.boundary ℝ = C.pieces i ∧ Q.boundary ℝ = D.pieces j ∧
      IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      IsFinitePLBallPair P2 (closure Q.inside) (Q.boundary ℝ) ∧
      closure P.inside ⊆ interior K \ B ∧
      closure Q.inside ⊆ interior J ∧
      g '' P.boundary ℝ = f '' Q.boundary ℝ ∧
      closure P.inside ∩ (K ∩ g ⁻¹' (f '' J)) = P.boundary ℝ ∧
      Disjoint P.inside (K ∩ g ⁻¹' (f '' J)) := by
  classical
  let := C.components_finite
  let := D.components_finite
  have hCsub (i) : C.pieces i ⊆ K := fun x hx =>
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hDsub (i) : D.pieces i ⊆ J := fun x hx =>
    (D.right_space.subset (D.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hCcover : (⋃ i, C.pieces i) = K ∩ g ⁻¹' (f '' J) :=
    C.cover.symm.trans C.right_space
  obtain ⟨i,n,P,hPi,hP,hPb,hPball,hPin,hPinter,hPavoid⟩ :=
    exists_innermost_region_disk_of_mixed_contacts C.pieces C.disjoint
      (Rim := B) (U := interior K \ B)
      (disjoint_left.mpr fun _ hx hy => hy.2 hx) C.models hgood
  have hclosed : Disjoint (C.pieces i) B := by
    apply disjoint_left.mpr
    intro x hx hxr
    exact (hPin (hPball.1 (hPb.symm.subset hx))).2 hxr
  obtain ⟨c,hc⟩ := C.exists_component_equiv D
  let j := c.symm i
  have hphysical : f '' D.pieces j = g '' P.boundary ℝ := by
    rw [hc,hPb]
    simp only [j,c.apply_symm_apply]
  have hclosedD : Disjoint (D.pieces j) (frontier J) := by
    apply disjoint_left.mpr
    intro x hx hxr
    obtain ⟨y,hy,hyx⟩ := hphysical.subset ⟨x,hx,rfl⟩
    have hyC := hPb.subset hy
    exact disjoint_left.mp hclosed hyC
      ((hrims x (hDsub j hx) y (hCsub i hyC) hyx.symm).mp hxr)
  have hQmodel : ∃ (m : ℕ) (Q : Polygon P2 (m+3)),
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧ Q.boundary ℝ = D.pieces j := by
    rcases D.models j with hj | ⟨m,Q,hQi,hQ,hQb,_⟩
    · obtain ⟨u,v,_,huv⟩ := hj.exists_boundary_eq_pair
      have hu := huv.symm.subset (show u ∈ ({u,v} : Set P2) from Or.inl rfl)
      exact (disjoint_left.mp hclosedD hu.1 hu.2).elim
    · exact ⟨m,Q,hQi,hQ,hQb⟩
  obtain ⟨m,Q,hQi,hQ,hQb⟩ := hQmodel
  have hQboundary : Q.boundary ℝ ⊆ interior J := by
    intro x hx
    have hxj := hQb.subset hx
    exact (mem_interior_iff_notMem_frontier (hDsub j hxj)).mpr
      (fun hxfr => disjoint_left.mp hclosedD hxj hxfr)
  have hQin : closure Q.inside ⊆ interior J :=
    Q.closure_inside_subset_convex hQ hQi hJ.interior (by
      rintro _ ⟨v,rfl⟩
      exact hQboundary (mem_iUnion.mpr ⟨v,left_mem_affineSegment ℝ _ _⟩))
  refine ⟨i,j,n,m,P,Q,hPi,hP,hQi,hQ,hPb,hQb,hPball,
    Q.isFinitePLBallPair_closed_inside hQ hQi,hPin,hQin,?_,
    hCcover ▸ hPinter,hCcover ▸ hPavoid⟩
  rw [hQb]
  exact hphysical.symm

end PoincareConjecture.M76

