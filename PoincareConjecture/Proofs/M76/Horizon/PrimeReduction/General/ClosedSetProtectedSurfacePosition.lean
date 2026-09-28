import PoincareConjecture.Proofs.M76.PrimeReduction.FiniteSurfaceEdgeContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ClosedSetProtectedPosition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds

set_option autoImplicit false

open Set Module unitInterval Topology

namespace Geometry.SimplicialComplex

theorem exists_closed_set_protected_surface_edge_position_with_height
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (J P P₀ T : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite)
    (hP₀ : P₀.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    {Z : Set E} (hZ : IsClosed Z)
    (hnear : ∀ x : P.space, (x : E) ∈ Z →
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ 𝓝 x)
    (height : E →ᵃ[ℝ] ℝ)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P₀.space T.vertices)
    (hedges : ∀ t ∈ T.faces, t.card = 2 →
      (P₀.space ∩ convexHull ℝ (t : Set E)).Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (K K₀ : SimplicialComplex ℝ E)
      (H : PLCarrierMotion J.space P₀.space ε) (A : SimplicialComplex ℝ E),
      K.faces.Finite ∧ K.space = P.space ∧
      (∀ s ∈ K.faces, s.card ≤ 3) ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      K.AffineOnFaces (H.map 1) ∧
      (∀ τ v, v ∈ K.vertices →
        (height v < 0 → height (H.map τ v) < 0) ∧
        (0 < height v → 0 < height (H.map τ v))) ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ s ∈ A.faces, s.card ≤ 3) ∧
      (∀ s ∈ A.faces,
        convexHull ℝ (s : Set E) ⊆ P₀.space ∨
          ∀ t ∈ T.faces, affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
              (convexHull ℝ (t : Set E))) ∧
      Disjoint A.space T.vertices ∧
      (∀ t ∈ T.faces, t.card ≤ 2 →
        (A.space ∩ convexHull ℝ (t : Set E)).Finite) ∧
      {x | x ∈ A.space ∧ ∃ t ∈ T.faces, t.card ≤ 2 ∧
        x ∈ convexHull ℝ (t : Set E)}.Finite ∧
      (∀ τ, EqOn (H.map τ) id Z) ∧
      ∃ U : Set E, IsOpen U ∧ Z ⊆ U ∧ ∀ τ, EqOn (H.map τ) id U := by
  classical
  obtain ⟨R, K, K₀, hR, _, hKR, hKs, hK₀K, hK₀s, hfull,
      H, hH, _, hHZ, hHU, hsign, hpos⟩ :=
    J.exists_closed_set_protected_finite_polyhedron_position_with_height P P₀ hJ hP hP₀ hcv
      hP₀P hPJ hfront hZ hnear (fun _ : Unit => T) (fun _ => hT) height hε
  have hK : K.faces.Finite := hR.subset hKR
  let B : Finset (AffineSubspace ℝ E) :=
    hP.toFinset.image (fun s : Finset E => affineSpan ℝ (s : Set E))
  have hB (V : AffineSubspace ℝ E) (hV : V ∈ B) : finrank ℝ V.direction ≤ 2 := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hV
    have hsP := hP.mem_toFinset.mp hs
    exact finrank_affineSpan_finset_le (P.nonempty_of_mem_faces hsP) (hcard s hsP)
  have hcover (x : E) (hx : x ∈ K.space) : ∃ V ∈ B, x ∈ V := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hKs.subset hx)
    exact ⟨affineSpan ℝ (s : Set E), Finset.mem_image.mpr
      ⟨s, hP.mem_toFinset.mpr hs, rfl⟩, convexHull_subset_affineSpan (s := (s : Set E)) hxs⟩
  have hKcard (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 :=
    K.face_card_le_of_finite_affine_cover B hB hcover hs
  have hHK : K.AffineOnFaces (H.map 1) := fun s hs => hH s (hKR hs)
  have hinj : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let A := hHK.embeddedImage hinj
  have hA : A.faces.Finite := hHK.embeddedImage_finite hinj hK
  have hAs : A.space = H.map 1 '' P.space := by
    rw [hHK.embeddedImage_space, hKs]
  have hAcard (s : Finset E) (hs : s ∈ A.faces) : s.card ≤ 3 := by
    rw [hHK.embeddedImage_faces hinj] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans (hKcard t ht)
  have hApos (s : Finset E) (hs : s ∈ A.faces) :
      convexHull ℝ (s : Set E) ⊆ P₀.space ∨
        ∀ t ∈ T.faces, affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
            (convexHull ℝ (t : Set E)) := by
    rw [hHK.embeddedImage_faces hinj] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    by_cases hu₀ : u ∈ K₀.faces
    · left
      have hufix : u.image (H.map 1) = u := by
        calc
          u.image (H.map 1) = u.image id := by
            apply Finset.image_congr
            intro x hx
            exact H.fixed_protected 1 x (hK₀s.subset (K₀.subset_space hu₀ hx))
          _ = u := Finset.image_id
      change convexHull ℝ ((u.image (H.map 1)) : Set E) ⊆ P₀.space
      rw [hufix]
      exact (K₀.convexHull_subset_space hu₀).trans hK₀s.subset
    · right
      intro t ht
      simpa only [Finset.coe_image] using hpos () u hu hu₀ t ht
  have hprotected (t : Finset E) (ht : t ∈ T.faces) (htc : t.card ≤ 2) :
      (P₀.space ∩ convexHull ℝ (t : Set E)).Finite := by
    by_cases he : t.card = 2
    · exact hedges t ht he
    · have hone : t.card = 1 := by
        have := Finset.card_pos.mpr (T.nonempty_of_mem_faces ht)
        omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      apply (Set.finite_singleton v).subset
      intro x hx
      simpa only [Finset.coe_singleton, convexHull_singleton] using hx.2
  obtain ⟨havoid, hfinite⟩ :=
    A.vertex_avoidance_and_finite_edge_contacts T hA hdim hAcard hvertices hprotected hApos
  refine ⟨K, K₀, H, A, hK, hKs, hKcard, hK₀K, hK₀s, hfull, hHK,
    (fun τ v hv => hsign τ v (hKR hv)),
    hA, hAs, hAcard, hApos, havoid, hfinite, ?_, hHZ, hHU⟩
  let S : Set (Finset E) := {t | t ∈ T.faces ∧ t.card ≤ 2}
  have hS : S.Finite := hT.subset (fun _ ht => ht.1)
  apply (hS.biUnion (fun t ht => hfinite t ht.1 ht.2)).subset
  rintro x ⟨hx, t, ht, htc, hxt⟩
  exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨⟨ht, htc⟩, ⟨hx, hxt⟩⟩⟩

theorem exists_closed_set_protected_surface_edge_position
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (J P P₀ T : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite)
    (hP₀ : P₀.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    {Z : Set E} (hZ : IsClosed Z)
    (hnear : ∀ x : P.space, (x : E) ∈ Z →
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ 𝓝 x)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P₀.space T.vertices)
    (hedges : ∀ t ∈ T.faces, t.card = 2 →
      (P₀.space ∩ convexHull ℝ (t : Set E)).Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H : PLCarrierMotion J.space P₀.space ε) (A : SimplicialComplex ℝ E),
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ s ∈ A.faces, s.card ≤ 3) ∧
      (∀ s ∈ A.faces,
        convexHull ℝ (s : Set E) ⊆ P₀.space ∨
          ∀ t ∈ T.faces, affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
              (convexHull ℝ (t : Set E))) ∧
      Disjoint A.space T.vertices ∧
      (∀ t ∈ T.faces, t.card ≤ 2 →
        (A.space ∩ convexHull ℝ (t : Set E)).Finite) ∧
      {x | x ∈ A.space ∧ ∃ t ∈ T.faces, t.card ≤ 2 ∧
        x ∈ convexHull ℝ (t : Set E)}.Finite ∧
      (∀ τ, EqOn (H.map τ) id Z) ∧
      ∃ U : Set E, IsOpen U ∧ Z ⊆ U ∧ ∀ τ, EqOn (H.map τ) id U := by

  obtain ⟨K, K₀, H, A, _, _, _, _, _, _, _, _, hA⟩ :=
    exists_closed_set_protected_surface_edge_position_with_height hdim J P P₀ T
      hJ hP hP₀ hT hcv hP₀P hPJ hfront hZ hnear 0 hcard hvertices hedges hε
  exact ⟨H, A, hA⟩

end Geometry.SimplicialComplex
