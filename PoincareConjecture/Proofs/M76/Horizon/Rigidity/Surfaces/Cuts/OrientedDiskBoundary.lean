import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Planar.PairedTriangleDeterminants
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.NumberedTriangleParity
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.SignParity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]



theorem planar_ordered_edge_determinants
    (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (basis : Module.Basis (Fin 3) ℝ F)
    (ell : F →ᴬ[ℝ] ℝ) (n : F) (hn : ell.contLinear n = 1)
    (hplane : ∀ x ∈ K.space, ell (f x) = 0)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = 2) (htc : t.card = 3) (huc : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (p r : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hpt : Finset.univ.image p = t) (hru : Finset.univ.image r = u)
    (i j : Fin 3)
    (hsi : (Finset.univ.erase i).image p = s)
    (hsj : (Finset.univ.erase j).image r = s)
    (horder : p ∘ i.succAbove = r ∘ j.succAbove) :
    ((-1 : ℝ) ^ i.val * basis.det ![f (p 1) - f (p 0), f (p 2) - f (p 0), n]) *
      ((-1 : ℝ) ^ j.val * basis.det ![f (r 1) - f (r 0), f (r 2) - f (r 0), n]) < 0 := by
  classical
  let perm : Fin 3 → Fin 3 := ![i.succAbove 0, i.succAbove 1, i]
  have hperm : Function.Injective perm := by fin_cases i <;> decide
  let p' : Fin 3 → E := p ∘ perm
  have hp' : AffineIndependent ℝ p' := hp.comp_embedding ⟨perm, hperm⟩
  have hp't (k : Fin 3) : p' k ∈ t := by
    rw [← hpt]
    exact Finset.mem_image.mpr ⟨perm k, Finset.mem_univ _, rfl⟩
  have hsp (x : E) (hx : x ∈ s) : x = p' 0 ∨ x = p' 1 := by
    rw [← hsi] at hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hk).1
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨v, hvs, huv, hdet⟩ := hf.exists_opposite_triangle_determinants K f hi
    basis ell n hn hplane hs ht hu hsc htc huc hst hsu htu p' hp' hp't hsp
  have hvj : v = r j := by
    have hvu : v ∈ u := by simp only [huv, Finset.mem_insert, true_or]
    rw [← hru] at hvu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hvu
    by_cases hkj : k = j
    · exact congrArg r hkj
    · exact (hvs (hsj ▸ Finset.mem_image.mpr
        ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩, rfl⟩)).elim
  have h0 : p (i.succAbove 0) = r (j.succAbove 0) := congrFun horder 0
  have h1 : p (i.succAbove 1) = r (j.succAbove 1) := congrFun horder 1
  have hpdet := triangle_boundary_determinant basis (f ∘ p) n i
  have hrDet := triangle_boundary_determinant basis (f ∘ r) n j
  dsimp only [Function.comp_apply] at hpdet hrDet
  have hcombined := congrArg₂ (fun a b : ℝ ↦ a * b) hpdet hrDet
  apply lt_of_eq_of_lt hcombined.symm
  simpa [p', perm, hvj, h0, h1] using hdet



theorem exists_planar_all_edge_signs_for_numbering
    (K : SimplicialComplex ℝ E) (number : K.vertices ↪ ℕ)
    (f : E → F) (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (basis : Module.Basis (Fin 3) ℝ F)
    (ell : F →ᴬ[ℝ] ℝ) (n : F) (hn : ell.contLinear n = 1)
    (hplane : ∀ x ∈ K.space, ell (f x) = 0) :
    ∃ (sigma : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
      ∀ (t u : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
          K.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
        ∀ s : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          s.val ⊆ t.val → s.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val s.val) +
            (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  classical
  let V := K.vertices
  let Q := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have henumerate (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) :=
    exists_numbered_triangle_enumeration number t.val t.property.2
  choose p hpinj hpimage hpmono using henumerate
  let v : V ↪ E := Function.Embedding.subtype _
  let face (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) := t.val.map v
  let point (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) : Fin 3 → E :=
    v ∘ p t
  have hface (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) :
      face t ∈ K.faces := t.property.1
  have hpointimage (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) :
      Finset.univ.image (point t) = face t := by
    dsimp only [point, face]
    rw [Finset.image_comp, hpimage]
    exact (Finset.map_eq_image _ _).symm
  have hpointmem (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) (k : Fin 3) :
      point t k ∈ face t := by
    rw [← hpointimage]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hpointindep (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) :
      AffineIndependent ℝ (point t) := by
    let emb : Fin 3 ↪ face t := ⟨fun k ↦ ⟨point t k, hpointmem t k⟩, by
      intro k l he
      exact hpinj t (v.injective (congrArg (fun z : face t ↦ (z : E)) he))⟩
    exact (K.indep (hface t)).comp_embedding emb
  let det (t : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) :=
    basis.det ![f (point t 1) - f (point t 0), f (point t 2) - f (point t 0), n]
  refine ⟨fun t ↦ orientationSignParity (SignType.sign (det t)), ?_⟩
  intro t u htu s hst hsu
  obtain ⟨i, hi⟩ := exists_triangle_edge_deleted_index (p t) (hpinj t) s.val t.val
    (hpimage t) hst s.property.2
  obtain ⟨j, hj⟩ := exists_triangle_edge_deleted_index (p u) (hpinj u) s.val u.val
    (hpimage u) hsu s.property.2
  have hedgeorder := numbered_triangle_common_edge_order number (p t) (p u)
    (hpmono t) (hpmono u) i j (hi.trans hj.symm)
  have hgeomi : (Finset.univ.erase i).image (point t) = s.val.map v := by
    dsimp only [point]
    rw [Finset.image_comp, hi]
    exact (Finset.map_eq_image _ _).symm
  have hgeomj : (Finset.univ.erase j).image (point u) = s.val.map v := by
    dsimp only [point]
    rw [Finset.image_comp, hj]
    exact (Finset.map_eq_image _ _).symm
  have hgeomorder : point t ∘ i.succAbove = point u ∘ j.succAbove := by
    funext k
    exact congrArg v (congrFun hedgeorder k)
  have hfacecard (a : PreAbstractSimplicialComplex.ModTwoCochains.Triangle Q) :
      (face a).card = 3 := by
    dsimp only [face]
    rw [Finset.card_map]
    exact a.property.2
  have hgeomneq : face t ≠ face u := fun he ↦
    htu (Subtype.ext (Finset.map_injective v he))
  have hdet := planar_ordered_edge_determinants K f hf ‹InjOn f K.space›
    basis ell n hn hplane s.property.1 (hface t) (hface u)
    (by simpa using s.property.2) (hfacecard t) (hfacecard u)
    (Finset.map_subset_map.mpr hst) (Finset.map_subset_map.mpr hsu) hgeomneq
    (point t) (point u) (hpointindep t) (hpointimage t) (hpointimage u)
    i j hgeomi hgeomj hgeomorder
  have hparityt := boundaryFaceParity_ordered_triangle number (p t) (hpinj t) (hpmono t) i
  have hparityu := boundaryFaceParity_ordered_triangle number (p u) (hpinj u) (hpmono u) j
  rw [hpimage t, hi] at hparityt
  rw [hpimage u, hj] at hparityu
  dsimp only
  rw [hparityt, hparityu]
  simpa only [one_mul] using orientationSignParity_of_common_label
    (det t) (det u) 1 (by decide) i j hdet



theorem exists_planar_all_edge_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E → F) (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (basis : Module.Basis (Fin 3) ℝ F)
    (ell : F →ᴬ[ℝ] ℝ) (n : F) (hn : ell.contLinear n = 1)
    (hplane : ∀ x ∈ K.space, ell (f x) = 0) :
    ∃ (number : K.vertices ↪ ℕ)
      (sigma : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
      ∀ (t u : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
          K.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
        ∀ s : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          s.val ⊆ t.val → s.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val s.val) +
            (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  classical
  let := (K.finite_vertices_of_finite_faces hK).fintype
  let number : K.vertices ↪ ℕ :=
    ⟨fun v ↦ (Fintype.equivFin K.vertices v).val, fun _ _ h ↦
      (Fintype.equivFin K.vertices).injective (Fin.ext h)⟩
  obtain ⟨sigma, hsigma⟩ := exists_planar_all_edge_signs_for_numbering K number f hf hi
    basis ell n hn hplane
  exact ⟨number, sigma, hsigma⟩



theorem coherent_triangle_signs_global_difference
    {V : Type*} [DecidableEq V] (A : PreAbstractSimplicialComplex V)
    (number : V → ℕ) (hconn : (triangleGraph A).Connected)
    (sigma tau : PreAbstractSimplicialComplex.ModTwoCochains.Triangle A → ZMod 2)
    (hsigma : ∀ t u, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (htau : ∀ t u, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (tau t + boundaryFaceParity number t.val s.val) +
        (tau u + boundaryFaceParity number u.val s.val) = 1) :
    ∃ c : ZMod 2, ∀ t, sigma t + tau t = c := by
  have hedge {t u} (htu : (triangleGraph A).Adj t u) :
      sigma t + tau t = sigma u + tau u := by
    obtain ⟨hne, s, hst, hsu⟩ := htu
    have hs := hsigma t u hne s hst hsu
    have ht := htau t u hne s hst hsu
    linear_combination (norm := ring_nf) hs + ht
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, sub_zero]
  have hwalk {t u} (w : (triangleGraph A).Walk t u) :
      sigma t + tau t = sigma u + tau u := by
    induction w with
    | nil => rfl
    | cons hadj w ih => exact (hedge hadj).trans ih
  obtain ⟨root⟩ := hconn.nonempty
  refine ⟨sigma root + tau root, fun t ↦ ?_⟩
  obtain ⟨w⟩ := hconn.preconnected t root
  exact hwalk w

end PoincareConjecture.M76.OriginalTriangleCopies
