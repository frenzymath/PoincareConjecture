import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_finitePL_subpolyhedron_extension
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {S : Set E}
    (hSK : S ⊆ K.space) {f : E → F} (hf : FinitePiecewiseAffineOn f S) :
    ∃ g : E → F, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S := by
  classical
  obtain ⟨J, hJ, hJS, hfJ⟩ := hf
  let : Fintype J.faces := hJ.fintype
  choose H hH using fun t : J.faces ↦
    t.val.exists_affine_halfspaces_convexHull (J.indep t.property)
  let Htotal := Finset.univ.biUnion H
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRK, _, hRH⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hN Htotal
  obtain ⟨g, hg, hgv⟩ := R.exists_affineOnFaces_eqOn_vertices f
  refine ⟨g, ⟨R, hR, hRK.space_eq, hg⟩, ?_⟩
  intro x hx
  have hxR : x ∈ R.space := hRK.space_eq.symm ▸ hSK hx
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp (hJS.symm ▸ hx)
  let i : J.faces := ⟨t, ht⟩
  have hHi : ∀ A ∈ H i, R.RespectsAffineHyperplane A := fun A hA ↦
    hRH A (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩)
  have hxH : ∀ A ∈ H i, A x ≤ 0 := by
    change x ∈ {y | ∀ A ∈ H i, A y ≤ 0}
    rw [← hH i]
    exact hxt
  obtain ⟨s, hs, hxs, hsH⟩ := R.exists_face_in_halfspaces (H i) hHi hxR hxH
  have hst : (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
    intro v hv
    rw [hH i]
    exact hsH v hv
  have hverts : (s : Set E) ⊆ R.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs
  obtain ⟨a, ha⟩ := hg s hs
  obtain ⟨b, hb⟩ := hfJ t ht
  have hab : EqOn a.toAffineMap b.toAffineMap (s : Set E) := by
    intro v hv
    exact (ha (subset_convexHull ℝ _ hv)).symm.trans
      ((hgv (hverts hv)).trans (hb (hst hv)))
  have hxold : x ∈ convexHull ℝ (t : Set E) :=
    convexHull_min hst (convex_convexHull ℝ _) hxs
  exact (ha hxs).trans
    ((AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hxs)).trans
      (hb hxold).symm)

end Geometry.SimplicialComplex

namespace Set

variable {M E F : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsFinitePLBallPair.exists_boundary_height_extension
    {s b d : Set E} (hs : IsFinitePLBallPair M s b) (hdb : d ⊆ b)
    {f : E → F} (hf : FinitePiecewiseAffineOn f d) :
    ∃ g : E → F, FinitePiecewiseAffineOn g s ∧ EqOn g f d := by
  have htri := hs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := htri
  obtain ⟨g, hg, hgf⟩ := K.exists_finitePL_subpolyhedron_extension hK
    ((hdb.trans hs.1).trans hKs.symm.subset) hf
  exact ⟨g, hKs ▸ hg, hgf⟩

theorem IsFinitePLBallPair.exists_boundary_graph_lift [FiniteDimensional ℝ F]
    {s b d : Set E} (hs : IsFinitePLBallPair M s b) (hdb : d ⊆ b)
    {f : E → F} (hf : FinitePiecewiseAffineOn f d) :
    ∃ g : E → F,
      FinitePiecewiseAffineOn g s ∧ EqOn g f d ∧
      FinitePiecewiseAffineOn (fun x ↦ (x, g x)) s ∧
      IsFinitePLBallPair M ((fun x ↦ (x, g x)) '' s) ((fun x ↦ (x, g x)) '' b) ∧
      (fun x ↦ (x, g x)) '' d = (fun x ↦ (x, f x)) '' d ∧
      Prod.fst '' ((fun x ↦ (x, g x)) '' s) = s := by
  obtain ⟨g, hg, hgf⟩ := hs.exists_boundary_height_extension hdb hf
  have hid : FinitePiecewiseAffineOn (id : E → E) s := by
    obtain ⟨K, hK, hKs, _⟩ := hg
    exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  have hgraph := hid.prod_mk hg
  have hinj : Function.Injective (fun x ↦ (x, g x)) := fun _ _ h ↦ congrArg Prod.fst h
  refine ⟨g, hg, hgf, hgraph, hs.image hgraph hinj.injOn, ?_, ?_⟩
  · exact Set.image_congr (fun x hx ↦ Prod.ext rfl (hgf hx))
  · rw [← image_comp]
    exact image_id s

end Set
