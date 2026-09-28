import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.PolygonSignPreservation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.FiniteVertexSignBudget
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem ncard_polygon_composed_zero_eq_two_of_strict_sign_preservation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 2)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPK : P.boundary ℝ = K.space)
    (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ) {f : E → F}
    (hf : K.AffineOnFaces f)
    (hn : IsPreconnected (K.space ∩ {x | A x < 0}))
    (hp : IsPreconnected (K.space ∩ {x | 0 < A x}))
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B (f v))
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B (f v) < 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 →
      v ∈ closure (K.space ∩ {x | A x < 0}) ∧
        v ∈ closure (K.space ∩ {x | 0 < A x}))
    (hedges : ∀ s ∈ K.faces, s.card = 2 → ∃ v ∈ s, A v ≠ 0)
    (hnegn : ∃ v ∈ K.vertices, A v < 0)
    (hposn : ∃ v ∈ K.vertices, 0 < A v) :
    (K.space ∩ {x | B (f x) = 0}).ncard = 2 := by
  classical
  let g : E → E × F := fun x => (x, f x)
  have hgi : Function.Injective g := fun _ _ h => congrArg Prod.fst h
  have hg : K.AffineOnFaces g := by
    intro s hs
    obtain ⟨a, ha⟩ := hf s hs
    exact ⟨(ContinuousAffineMap.id ℝ E).prod a, fun x hx => Prod.ext rfl (ha hx)⟩
  have hgPL := hg.finitePiecewiseAffineOn hK
  have hgc : ContinuousOn g K.space := hgPL.continuousOn
  let L := hg.embeddedImage hgi.injOn
  have hL : L.faces.Finite := hg.embeddedImage_finite hgi.injOn hK
  have hLs : L.space = g '' K.space := hg.embeddedImage_space hgi.injOn
  have hLv : L.vertices = g '' K.vertices := hg.embeddedImage_vertices hgi.injOn
  have hLf : L.faces = (fun s : Finset E => s.image g) '' K.faces :=
    hg.embeddedImage_faces hgi.injOn
  have hLbound (s : Finset (E × F)) (hs : s ∈ L.faces) : s.card ≤ 2 := by
    rw [hLf] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans (hbound t ht)
  let A' : E × F →ᵃ[ℝ] ℝ := A.comp (LinearMap.fst ℝ E F).toAffineMap
  let B' : E × F →ᵃ[ℝ] ℝ := B.comp (LinearMap.snd ℝ E F).toAffineMap
  have hsection (S : Set ℝ) :
      g '' (K.space ∩ A ⁻¹' S) = L.space ∩ A' ⁻¹' S := by
    rw [hLs]
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxA⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hxA⟩
    · rintro ⟨⟨x, hx, rfl⟩, hxA⟩
      exact ⟨x, ⟨hx, hxA⟩, rfl⟩
  have hnL : IsPreconnected (L.space ∩ {x | A' x < 0}) := by
    change IsPreconnected (L.space ∩ A' ⁻¹' Iio 0)
    rw [← hsection (Iio 0)]
    exact hn.image g (hgc.mono inter_subset_left)
  have hpL : IsPreconnected (L.space ∩ {x | 0 < A' x}) := by
    change IsPreconnected (L.space ∩ A' ⁻¹' Ioi 0)
    rw [← hsection (Ioi 0)]
    exact hp.image g (hgc.mono inter_subset_left)
  have hpvL (v : E × F) (hv : v ∈ L.vertices) (hvA : 0 < A' v) : 0 < B' v := by
    rw [hLv] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact hpos x hx hvA
  have hnvL (v : E × F) (hv : v ∈ L.vertices) (hvA : A' v < 0) : B' v < 0 := by
    rw [hLv] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact hneg x hx hvA
  have hzL (v : E × F) (hv : v ∈ L.vertices) (hvA : A' v = 0) :
      v ∈ closure (L.space ∩ {x | A' x < 0}) ∧
        v ∈ closure (L.space ∩ {x | 0 < A' x}) := by
    rw [hLv] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨hxn, hxp⟩ := hzero x hx hvA
    have hc := hgc x (K.vertices_subset_space hx)
    constructor
    · change g x ∈ closure (L.space ∩ A' ⁻¹' Iio 0)
      rw [← hsection (Iio 0)]
      exact (hc.mono inter_subset_left).mem_closure_image hxn
    · change g x ∈ closure (L.space ∩ A' ⁻¹' Ioi 0)
      rw [← hsection (Ioi 0)]
      exact (hc.mono inter_subset_left).mem_closure_image hxp
  have heL (s : Finset (E × F)) (hs : s ∈ L.faces) (hsc : s.card = 2) :
      ∃ v ∈ s, A' v ≠ 0 := by
    rw [hLf] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have htc : t.card = 2 := by
      simpa only [Finset.card_image_of_injective _ hgi] using hsc
    obtain ⟨v, hv, hvA⟩ := hedges t ht htc
    exact ⟨g v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hvA⟩
  have hnnL : ∃ v ∈ L.vertices, A' v < 0 := by
    obtain ⟨v, hv, hvA⟩ := hnegn
    exact ⟨g v, hLv.symm.subset ⟨v, hv, rfl⟩, hvA⟩
  have hpnL : ∃ v ∈ L.vertices, 0 < A' v := by
    obtain ⟨v, hv, hvA⟩ := hposn
    exact ⟨g v, hLv.symm.subset ⟨v, hv, rfl⟩, hvA⟩
  obtain ⟨N, Q, hQi, hQ, hQs⟩ := P.exists_polygon_finitePL_image hP hinj
    hgPL hPK.subset hgi.injOn
  have hQL : Q.boundary ℝ = L.space := by rw [hQs, hPK, hLs]
  have hcount := L.ncard_polygon_zero_eq_two_of_strict_sign_preservation hL hLbound
    Q hQ hQi hQL A' B' hnL hpL hpvL hnvL hzL heL hnnL hpnL
  have hnew : L.space ∩ {x | B' x = 0} = g '' (K.space ∩ {x | B (f x) = 0}) := by
    rw [hLs]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxB⟩
      exact ⟨x, ⟨hx, hxB⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxB⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hxB⟩
  rw [hnew, Set.ncard_image_of_injective _ hgi] at hcount
  exact hcount



theorem ncard_face_affine_polygon_image_zero_eq_two
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 2)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPK : P.boundary ℝ = K.space)
    (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ) {f : E → F}
    (hf : K.AffineOnFaces f) (hfi : InjOn f K.space)
    (hn : IsPreconnected (K.space ∩ {x | A x < 0}))
    (hp : IsPreconnected (K.space ∩ {x | 0 < A x}))
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B (f v))
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B (f v) < 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 →
      v ∈ closure (K.space ∩ {x | A x < 0}) ∧
        v ∈ closure (K.space ∩ {x | 0 < A x}))
    (hedges : ∀ s ∈ K.faces, s.card = 2 → ∃ v ∈ s, A v ≠ 0)
    (hnegn : ∃ v ∈ K.vertices, A v < 0)
    (hposn : ∃ v ∈ K.vertices, 0 < A v) :
    (f '' K.space ∩ {x | B x = 0}).ncard = 2 := by
  have hcount := K.ncard_polygon_composed_zero_eq_two_of_strict_sign_preservation hK hbound
    P hP hinj hPK A B hf hn hp hpos hneg hzero hedges hnegn hposn
  have hset : f '' K.space ∩ {x | B x = 0} = f '' (K.space ∩ {x | B (f x) = 0}) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxB⟩
      exact ⟨x, ⟨hx, hxB⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxB⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hxB⟩
  rw [hset, (hfi.mono inter_subset_left).ncard_image]
  exact hcount




theorem exists_polygon_zero_stability_radius
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 2)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPK : P.boundary ℝ = K.space)
    (A : E →ᵃ[ℝ] ℝ)
    (hn : IsPreconnected (K.space ∩ {x | A x < 0}))
    (hp : IsPreconnected (K.space ∩ {x | 0 < A x}))
    (hzero : ∀ v ∈ K.vertices, A v = 0 →
      v ∈ closure (K.space ∩ {x | A x < 0}) ∧
        v ∈ closure (K.space ∩ {x | 0 < A x}))
    (hedges : ∀ s ∈ K.faces, s.card = 2 → ∃ v ∈ s, A v ≠ 0)
    (hnegn : ∃ v ∈ K.vertices, A v < 0)
    (hposn : ∃ v ∈ K.vertices, 0 < A v) :
    ∃ δ > 0, ∀ f : E → E, K.AffineOnFaces f → InjOn f K.space →
      (∀ v ∈ K.vertices, dist (f v) v < δ) →
        (f '' K.space ∩ {x | A x = 0}).ncard = 2 := by
  obtain ⟨δ, hδ, hsign⟩ :=
    (K.finite_vertices_of_finite_faces hK).exists_strict_sign_preserving_radius
      A.continuous_of_finiteDimensional
  refine ⟨δ, hδ, fun f hf hfi hsmall => ?_⟩
  exact K.ncard_face_affine_polygon_image_zero_eq_two hK hbound P hP hinj hPK A A hf hfi
    hn hp (fun v hv => (hsign v hv (f v) (hsmall v hv)).2)
    (fun v hv => (hsign v hv (f v) (hsmall v hv)).1) hzero hedges hnegn hposn

end Geometry.SimplicialComplex
