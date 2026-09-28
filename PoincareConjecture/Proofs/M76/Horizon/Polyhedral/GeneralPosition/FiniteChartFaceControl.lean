import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.GeneralPosition.ConvexSegmentNeighborhood
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Metric Geometry

namespace OpenPartialHomeomorph

variable {X E V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_convex_affine_face_neighborhood (B : OpenPartialHomeomorph X V)
    (s : Finset E) (f : E → X) (A : E →ᴬ[ℝ] V) {Y : Set X} (hY : IsOpen Y)
    (hsource : MapsTo f (convexHull ℝ (s : Set E)) B.source)
    (hcoord : EqOn (B ∘ f) A (convexHull ℝ (s : Set E)))
    (hfY : MapsTo f (convexHull ℝ (s : Set E)) Y) :
    ∃ W : Set V, IsOpen W ∧ Convex ℝ W ∧ W ⊆ B.target ∧
      MapsTo B.symm W Y ∧ MapsTo A (convexHull ℝ (s : Set E)) W ∧
      MapsTo (B ∘ f) (convexHull ℝ (s : Set E)) W := by
  let C := A '' convexHull ℝ (s : Set E)
  have hCcompact : IsCompact C := (s.finite_toSet.isCompact_convexHull ℝ).image A.continuous
  have hCconvex : Convex ℝ C := (convex_convexHull ℝ _).affine_image A.toAffineMap
  have hCU : C ⊆ B.target ∩ B.symm ⁻¹' Y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hcoord hx]
    exact ⟨B.map_source (hsource hx), by
      change B.symm (B (f x)) ∈ Y
      rw [B.left_inv (hsource hx)]
      exact hfY hx⟩
  obtain ⟨δ, hδ, hsub⟩ := hCcompact.exists_thickening_subset_open
    (B.isOpen_inter_preimage_symm hY) hCU
  have hCW : C ⊆ thickening δ C := self_subset_thickening hδ C
  refine ⟨thickening δ C, isOpen_thickening, hCconvex.thickening δ,
    fun _ hx => (hsub hx).1, fun _ hx => (hsub hx).2, ?_, ?_⟩
  · intro x hx
    exact hCW ⟨x, hx, rfl⟩
  · intro x hx
    rw [hcoord hx]
    exact hCW ⟨x, hx, rfl⟩

theorem exists_finite_face_control
    {α κ : Type*} [Finite α] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (f : E → X) {Y : Set X}
    (hY : IsOpen Y) (hfY : MapsTo f K.space Y)
    (s : α → K.faces) (B : α → OpenPartialHomeomorph X V)
    (hsource : ∀ i, MapsTo f (convexHull ℝ ((s i).val : Set E)) (B i).source)
    (hcoord : ∀ i, ∃ A : E →ᴬ[ℝ] V,
      EqOn (B i ∘ f) A (convexHull ℝ ((s i).val : Set E)))
    (a b : κ → E) (hedge : ∀ k, {a k, b k} ∈ K.faces) :
    ∃ (W : α → Set V) (U : κ → Set X),
      (∀ i, IsOpen (W i) ∧ Convex ℝ (W i) ∧ W i ⊆ (B i).target ∧
        MapsTo (B i).symm (W i) Y ∧
        MapsTo (B i ∘ f) (convexHull ℝ ((s i).val : Set E)) (W i)) ∧
      (∀ k, IsOpen (U k) ∧ U k ⊆ Y ∧ MapsTo f (segment ℝ (a k) (b k)) (U k)) ∧
      ∀ k i, {a k, b k} ⊆ (s i).val → U k ⊆ (B i).source ∩ (B i) ⁻¹' W i := by
  classical
  choose A hA using hcoord
  choose W hWo hWc hWt hWY hAW hfW using fun i =>
    (B i).exists_convex_affine_face_neighborhood (s i).val f (A i) hY
      (hsource i) (hA i) (fun _ hx => hfY (K.convexHull_subset_space (s i).property hx))
  let U : κ → Set X := fun k => Y ∩ ⋂ i,
    if {a k, b k} ⊆ (s i).val then (B i).source ∩ (B i) ⁻¹' W i else univ
  have hinc (k : κ) (i : α) (hi : {a k, b k} ⊆ (s i).val) :
      U k ⊆ (B i).source ∩ (B i) ⁻¹' W i := by
    intro x hx
    simpa only [if_pos hi] using mem_iInter.mp hx.2 i
  refine ⟨W, U, fun i => ⟨hWo i, hWc i, hWt i, hWY i, hfW i⟩, ?_, hinc⟩
  intro k
  refine ⟨hY.inter (isOpen_iInter_of_finite fun i => ?_), inter_subset_left, ?_⟩
  · split_ifs
    · exact (B i).isOpen_inter_preimage (hWo i)
    · exact isOpen_univ
  · intro x hx
    have hxhull : x ∈ convexHull ℝ (({a k, b k} : Finset E) : Set E) := by
      simpa only [Finset.coe_pair, convexHull_pair] using hx
    refine ⟨hfY (K.convexHull_subset_space (hedge k) hxhull), mem_iInter.mpr ?_⟩
    intro i
    split_ifs with hi
    · have hxs : x ∈ convexHull ℝ ((s i).val : Set E) := convexHull_mono hi hxhull
      exact ⟨hsource i hxs, hfW i hxs⟩
    · exact mem_univ _

end OpenPartialHomeomorph
