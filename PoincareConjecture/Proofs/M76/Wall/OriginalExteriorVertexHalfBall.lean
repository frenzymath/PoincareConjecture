import PoincareConjecture.Proofs.M76.Wall.OriginalLocalBoundaryDual
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ExteriorHalfspaceChart

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_exterior_vertex_half_ball
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {C L : Set X} (hL : IsClosed L) (hLC : L ⊆ interior C)
    (K D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hDK : D ≤ K) (F : X → E) (H : (C \ interior L : Set X) ≃ₜ K.space)
    (g : E → (C \ interior L : Set X))
    (hHF : ∀ x : (C \ interior L : Set X), (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hD : D.space = F '' frontier L) {p : E} (hp : p ∈ D.vertices)
    (B : OpenPartialHomeomorph X V3) (hinside : B.source ⊆ interior C)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (A : V3 →L[ℝ] ℝ) (v : V3) (hv : A v = 1)
    (hhalf : ∀ y ∈ B.source, y ∈ L ↔ 0 ≤ A (B y)) :
    ∃ _G : BoundaryVertexHalfBall K D p,
      IsFinitePLBallPair (ℝ × ℝ) ((K.barycentricDualBlock {p}).link p).space
        (((K.barycentricDualBlock {p}).link p).space ∩ (D.barycentricDualBlock {p}).space) ∧
      IsFinitePLBallPair (ℝ × ℝ) (D.barycentricDualBlock {p}).space
        (((K.barycentricDualBlock {p}).link p).space ∩ (D.barycentricDualBlock {p}).space) := by
  have hfrontR : frontier L ⊆ C \ interior L :=
    fun _ hx => ⟨interior_subset (hLC (hL.frontier_subset hx)), hx.2⟩
  have hgF (x : X) (hx : x ∈ C \ interior L) : (g (F x) : X) = x := by
    have h := hg (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at h
    simpa only [hHF] using h
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩]
    exact (hHF (H.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨z, hz⟩))
  have hmark (z : E) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier L ↔ z ∈ D.space := by
    rw [hD]
    constructor
    · intro hzb
      exact ⟨g z, hzb, hFg z hz⟩
    · rintro ⟨x, hxb, hxz⟩
      rw [← hxz, hgF x (hfrontR hxb)]
      exact hxb
  let ell := A.toContinuousAffineMap
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [he] at hv'
    exact zero_ne_one hv'
  obtain ⟨hext, hboundary⟩ :=
    B.exterior_halfspace_and_frontier hinside ell hell hhalf
  have hnormal : (-ell).contLinear (-v) = 1 := by
    change -A (-v) = 1
    rw [map_neg, neg_neg, hv]
  have hlocal (z : E) (hz : z ∈ (K.closedStar p).space) :
      (g z : X) ∈ frontier (C \ interior L) ↔ z ∈ D.space := by
    exact (hboundary (g z) (hsource hz)).trans
      (hmark z (space_subset_of_le (show K.closedStar p ≤ K from fun _ hs => hs.1) hz))
  obtain ⟨G⟩ := exists_original_local_boundary_dual K D hDK H g hg hp B
    hsource hface hlocal (-ell) (-v) hnormal hext
  exact ⟨G, G.boundary_disks⟩

end PoincareConjecture.M76
