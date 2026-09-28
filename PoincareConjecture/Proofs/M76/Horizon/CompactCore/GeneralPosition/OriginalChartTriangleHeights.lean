import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.ZeroSet
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.TriangleRefinementOwners

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

theorem exists_original_chart_triangle_heights
    {E V X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hplanar : Module.finrank ℝ E = 2) (hconvex : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty)
    (C : κ → SimplicialComplex ℝ E) (hfaces : K.faces = ⋃ i, (C i).faces)
    (f : E → X) (B : κ → OpenPartialHomeomorph X V) (N F : Set X)
    (hsource : ∀ i, MapsTo f (C i).space (B i).source)
    (hcoords : ∀ i, (C i).AffineOnFaces (B i ∘ f))
    (hkind : ∀ i, Disjoint (B i).source F ∨ ∃ ell : V →ᵃ[ℝ] ℝ,
      (∀ y ∈ (B i).source, y ∈ N ↔ 0 ≤ ell (B i y)) ∧
      ∀ y ∈ (B i).source, y ∈ F ↔ ell (B i y) = 0) :
    ∃ (ell : κ → V →ᵃ[ℝ] ℝ) (owner : K.faces → κ) (A : Finset E → E →ᵃ[ℝ] ℝ),
      (∀ i y, y ∈ (B i).source → (y ∈ F ↔ ell i (B i y) = 0)) ∧
      (∀ i, ¬ Disjoint (B i).source F →
        ∀ y ∈ (B i).source, y ∈ N ↔ 0 ≤ ell i (B i y)) ∧
      (∀ t : K.faces, t.val ∈ (C (owner t)).faces) ∧
      (∀ t : K.faces, ∀ x ∈ convexHull ℝ (t.val : Set E),
        A t.val x = ell (owner t) (B (owner t) (f x))) ∧
      (∀ t ∈ K.faces, ∀ x ∈ convexHull ℝ (t : Set E), A t x = 0 ↔ f x ∈ F) ∧
      K.CompatibleTriangleZeroSets A ∧ K.triangleZeroSet A = K.space ∩ f ⁻¹' F := by
  classical
  have hell (i : κ) : ∃ ell : V →ᵃ[ℝ] ℝ,
      (∀ y ∈ (B i).source, y ∈ F ↔ ell (B i y) = 0) ∧
      (¬ Disjoint (B i).source F → ∀ y ∈ (B i).source, y ∈ N ↔ 0 ≤ ell (B i y)) := by
    rcases hkind i with hd | ⟨ell, hN, hF⟩
    · refine ⟨AffineMap.const ℝ V 1, ?_, fun h => (h hd).elim⟩
      intro y hy
      have hyF : y ∉ F := fun h => disjoint_left.mp hd hy h
      simp [hyF]
    · exact ⟨ell, hF, fun _ => hN⟩
  choose ell hell hside using hell
  have howner (t : K.faces) : ∃ i, t.val ∈ (C i).faces := by
    apply mem_iUnion.mp
    rw [← hfaces]
    exact t.property
  choose owner howner using howner
  choose D hD using fun t : K.faces => hcoords (owner t) t.val (howner t)
  let A : Finset E → E →ᵃ[ℝ] ℝ := fun t =>
    if ht : t ∈ K.faces then (ell (owner ⟨t, ht⟩)).comp (D ⟨t, ht⟩).toAffineMap
      else AffineMap.const ℝ E 1
  have hformula (t : K.faces) (x : E) (hx : x ∈ convexHull ℝ (t.val : Set E)) :
      A t.val x = ell (owner t) (B (owner t) (f x)) := by
    simp only [A, dif_pos t.property, AffineMap.comp_apply]
    exact congrArg (ell (owner t)) (hD t hx).symm
  have hzero (t : Finset E) (ht : t ∈ K.faces) (x : E)
      (hx : x ∈ convexHull ℝ (t : Set E)) : A t x = 0 ↔ f x ∈ F := by
    rw [hformula ⟨t, ht⟩ x hx]
    exact (hell _ _ (hsource _ (convexHull_subset_space (howner ⟨t, ht⟩) hx))).symm
  have hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := K.exists_full_coface_of_convex_space hK hconvex hne hs
    exact ⟨t, ht, by omega, hst⟩
  exact ⟨ell, owner, A, hell, hside, howner, hformula, hzero,
    K.compatibleTriangleZeroSets_of_common_preimage A f F (fun t ht _ => hzero t ht),
    K.triangleZeroSet_eq_preimage A f F hpure (fun t ht _ => hzero t ht)⟩

theorem original_chart_triangle_formula
    {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]
    (K T : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    (C : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
    (hCS : ∀ s, (C s).space ⊆ convexHull ℝ (s.val.val : Set E))
    (f : E → X) (B : {s : K.faces // s.val.card = 3} → OpenPartialHomeomorph X V)
    (ell : {s : K.faces // s.val.card = 3} → V →ᵃ[ℝ] ℝ)
    (owner : T.faces → {s : K.faces // s.val.card = 3})
    (A : Finset E → E →ᵃ[ℝ] ℝ)
    (howner : ∀ t : T.faces, t.val ∈ (C (owner t)).faces)
    (hformula : ∀ t : T.faces, ∀ x ∈ convexHull ℝ (t.val : Set E),
      A t.val x = ell (owner t) (B (owner t) (f x)))
    {s : {s : K.faces // s.val.card = 3}} {t : Finset E}
    (ht : t ∈ T.faces) (htC : t ∈ (C s).faces) (htcard : t.card = 3) :
    ∀ x ∈ convexHull ℝ (t : Set E), A t x = ell s (B s (f x)) := by
  have hown : owner ⟨t, ht⟩ = s :=
    K.refined_triangle_owner_unique hdim C hCS (howner ⟨t, ht⟩) htC htcard
  intro x hx
  simpa only [hown] using hformula ⟨t, ht⟩ x hx

end Geometry.SimplicialComplex
