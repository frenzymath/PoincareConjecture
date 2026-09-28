import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.ComponentMatching
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.Selection








set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q₀" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Q₁" => Set.ofPred (fun x : P2 => depth 8 x = 1)
local notation "Rim" => Q₀ ∪ Q₁

open Classical in
theorem exists_paired_circle_disks_of_one_marked_intersection
    {X : Type*} {f g : P2 → X}
    (C : SurfaceIntersectionComponents Ann Ann f g Rim)
    (D : SurfaceIntersectionComponents Ann Ann g f Rim)
    (hrims : ∀ x ∈ Ann, ∀ y ∈ Ann, f x = g y → (x ∈ Rim ↔ y ∈ Rim))
    (a b : P2)
    (hfirst_g : (Ann ∩ g ⁻¹' (f '' Ann)) ∩ Q₀ = {a})
    (hfirst_f : (Ann ∩ f ⁻¹' (g '' Ann)) ∩ Q₀ = {b})
    (hcircle : ∃ i, Disjoint (C.pieces i) Rim) :
    ∃ i j, ∃ (n m : ℕ) (P : Polygon P2 (n + 3)) (Q : Polygon P2 (m + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      P.boundary ℝ = C.pieces i ∧ Q.boundary ℝ = D.pieces j ∧
      IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      IsFinitePLBallPair P2 (closure Q.inside) (Q.boundary ℝ) ∧
      closure P.inside ⊆ {x : P2 | -1 < depth 8 x ∧ depth 8 x < 1} ∧
      closure Q.inside ⊆ {x : P2 | -1 < depth 8 x ∧ depth 8 x < 1} ∧
      g '' P.boundary ℝ = f '' Q.boundary ℝ ∧
      closure P.inside ∩ (Ann ∩ g ⁻¹' (f '' Ann)) = P.boundary ℝ ∧
      Disjoint P.inside (Ann ∩ g ⁻¹' (f '' Ann)) := by
  classical
  let := C.components_finite
  let := D.components_finite
  have hCsub (i) : C.pieces i ⊆ Ann := fun x hx =>
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hDsub (i) : D.pieces i ⊆ Ann := fun x hx =>
    (D.right_space.subset (D.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hCcover : (⋃ i, C.pieces i) = Ann ∩ g ⁻¹' (f '' Ann) :=
    C.cover.symm.trans C.right_space
  have hDcover : (⋃ i, D.pieces i) = Ann ∩ f ⁻¹' (g '' Ann) :=
    D.cover.symm.trans D.right_space
  obtain ⟨i,n,P,hPi,hP,hPb,hPball,hPinside,hPinter,hPavoid⟩ :=
    exists_innermost_disk_of_closed_intersection_component C.pieces C.disjoint
      (fun i x hx => mem_squareAnnulus_iff_depth.mp (hCsub i hx)) C.models a
      (hCcover ▸ hfirst_g) hcircle
  have hclosed : Disjoint (C.pieces i) Rim := by
    apply disjoint_left.mpr
    intro x hx hxr
    have hin := hPinside (hPball.1 (hPb.symm.subset hx))
    rcases hxr with h | h <;> change depth 8 x = _ at h <;> linarith [hin.1,hin.2]
  obtain ⟨c,hc⟩ := C.exists_component_equiv D
  let j := c.symm i
  have hphysical : f '' D.pieces j = g '' P.boundary ℝ := by
    rw [hc,hPb]
    simp only [j,c.apply_symm_apply]
  have hclosedD : Disjoint (D.pieces j) Rim := by
    apply disjoint_left.mpr
    intro x hx hxr
    obtain ⟨y,hy,hyx⟩ := hphysical.subset ⟨x,hx,rfl⟩
    have hyC := hPb.subset hy
    exact disjoint_left.mp hclosed hyC
      ((hrims x (hDsub j hx) y (hCsub i hyC) hyx.symm).mp hxr)
  have hQmodel : ∃ (m : ℕ) (Q : Polygon P2 (m + 3)),
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧ Q.boundary ℝ = D.pieces j := by
    rcases D.models j with hj | ⟨m,Q,hQi,hQ,hQb,_⟩
    · obtain ⟨u,v,_,huv⟩ := hj.exists_boundary_eq_pair
      have hu := huv.symm.subset (show u ∈ ({u,v} : Set P2) from Or.inl rfl)
      exact (disjoint_left.mp hclosedD hu.1 hu.2).elim
    · exact ⟨m,Q,hQi,hQ,hQb⟩
  obtain ⟨m,Q,hQi,hQ,hQb⟩ := hQmodel
  have hQboundary (x : P2) (hx : x ∈ Q.boundary ℝ) :
      -1 < depth 8 x ∧ depth 8 x < 1 := by
    have hxj := hQb.subset hx
    have hbounds := mem_squareAnnulus_iff_depth.mp (hDsub j hxj)
    exact ⟨lt_of_le_of_ne hbounds.1 (fun hh =>
      disjoint_left.mp hclosedD hxj (Or.inl hh.symm)),
      lt_of_le_of_ne hbounds.2 (fun hh => disjoint_left.mp hclosedD hxj (Or.inr hh))⟩
  have hQdis : Disjoint Q₀ Q₁ := disjoint_left.mpr fun x hx hy => by
    change depth 8 x = -1 at hx
    change depth 8 x = 1 at hy
    linarith
  obtain ⟨s,z,hb,hz,_,hs,_,_,_,_,_⟩ :=
    exists_unique_spanning_interval_of_one_marked_point D.pieces Q₀ Q₁ b hQdis
      D.disjoint (hDcover ▸ hfirst_f) D.models
  have hsQ : Disjoint (D.pieces s) (Q.boundary ℝ) := by
    rw [hQb]
    apply D.disjoint
    intro hsj
    exact disjoint_left.mp hclosedD (hsj ▸ hs.1 (Or.inl rfl)) (Or.inl hb)
  obtain ⟨hQball,hQinside⟩ := polygon_disk_of_disjoint_spanning_set Q hQ hQi hQboundary
    hs.isConnected.2 hsQ ⟨b,hs.1 (Or.inl rfl),hb⟩ ⟨z,hs.1 (Or.inr rfl),hz⟩
  refine ⟨i,j,n,m,P,Q,hPi,hP,hQi,hQ,hPb,hQb,hPball,hQball,hPinside,hQinside,?_,
    hCcover ▸ hPinter,hCcover ▸ hPavoid⟩
  rw [hQb]
  exact hphysical.symm

end PoincareConjecture.M76.Dehn.Annuli
