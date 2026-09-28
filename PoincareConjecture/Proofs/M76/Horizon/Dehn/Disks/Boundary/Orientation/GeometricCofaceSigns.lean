import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.StandardFrontierOrientation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.CofaceSideTransport









set_option autoImplicit false
open Set Geometry AbstractSimplicialComplex PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.Dehn

theorem boundaryFaceParity_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (number : W → ℕ) (s t : Finset V) :
    boundaryFaceParity number (s.map f) (t.map f) =
      boundaryFaceParity (number ∘ f) s t := by
  unfold boundaryFaceParity
  rw [← Finset.map_sdiff, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.filter_map, Finset.card_map]
  rfl



theorem exists_geometric_coface_signs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (A : SimplicialComplex ℝ E) (number : A.vertices ↪ ℕ)
    (sigma : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2)
    (hcancel : ∀ (t u : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex),
      t ≠ u → ∀ s : Edge A.vertexAbstractComplex.toPreAbstractSimplicialComplex,
        s.val ⊆ t.val → s.val ⊆ u.val →
        (sigma t + boundaryFaceParity number t.val s.val) +
          (sigma u + boundaryFaceParity number u.val s.val) = 1) :
    ∃ (label : E → ℕ) (sign : Finset E → ZMod 2), InjOn label A.vertices ∧
      ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
        ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
          (sign t + boundaryFaceParity label t s) +
            (sign u + boundaryFaceParity label u s) = 1 := by
  classical
  let v : A.vertices ↪ E := Function.Embedding.subtype _
  let label : E → ℕ := Function.extend v number (fun _ ↦ 0)
  have hlabel (x : A.vertices) : label x = number x := v.injective.extend_apply _ _ x
  let face : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex → Finset E :=
    fun t ↦ t.val.map v
  have hface : Function.Injective face := by
    intro t u h
    exact Subtype.ext (Finset.map_injective v h)
  let sign : Finset E → ZMod 2 := Function.extend face sigma (fun _ ↦ 0)
  have hsign (t : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
      sign (face t) = sigma t := hface.extend_apply _ _ t
  have hmap (s : Finset E) (hs : s ∈ A.faces) :
      (s.subtype (· ∈ A.vertices)).map v = s :=
    Finset.subtype_map_of_mem (fun x hx ↦ A.down_closed hs
      (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x))
  have hcard (s : Finset E) (hs : s ∈ A.faces) :
      (s.subtype (· ∈ A.vertices)).card = s.card := by
    exact (Finset.card_map v).symm.trans (congrArg Finset.card (hmap s hs))
  refine ⟨label, sign, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := number.injective (show number ⟨x, hx⟩ = number ⟨y, hy⟩ by
      rw [← hlabel, ← hlabel]; exact hxy)
    exact congrArg Subtype.val h
  · intro t ht htc u hu huc htu s hsc hst hsu
    have hs : s ∈ A.faces := A.down_closed ht hst (Finset.card_pos.mp (by omega))
    let t' : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex :=
      ⟨t.subtype (· ∈ A.vertices), by change _ ∈ A.faces; rw [hmap t ht]; exact ht,
        (hcard t ht).trans htc⟩
    let u' : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex :=
      ⟨u.subtype (· ∈ A.vertices), by change _ ∈ A.faces; rw [hmap u hu]; exact hu,
        (hcard u hu).trans huc⟩
    let s' : Edge A.vertexAbstractComplex.toPreAbstractSimplicialComplex :=
      ⟨s.subtype (· ∈ A.vertices), by change _ ∈ A.faces; rw [hmap s hs]; exact hs,
        (hcard s hs).trans hsc⟩
    have hne : t' ≠ u' := by
      intro h
      have hh := congrArg face h
      exact htu (by simpa only [face, t', u', hmap t ht, hmap u hu] using hh)
    have hsubt : s'.val ⊆ t'.val := by
      intro x hx
      exact Finset.mem_subtype.mpr (hst (Finset.mem_subtype.mp hx))
    have hsubu : s'.val ⊆ u'.val := by
      intro x hx
      exact Finset.mem_subtype.mpr (hsu (Finset.mem_subtype.mp hx))
    have h := hcancel t' u' hne s' hsubt hsubu
    have hnumber : label ∘ v = number := funext hlabel
    have hp (r : Finset A.vertices) :
        boundaryFaceParity label (r.map v) (s'.val.map v) =
          boundaryFaceParity number r s'.val := by
      rw [boundaryFaceParity_map, hnumber]
    rw [← hsign t', ← hsign u', ← hp t'.val, ← hp u'.val] at h
    simpa only [face, t', u', s', hmap t ht, hmap u hu, hmap s hs] using h



theorem exists_standard_frontier_geometric_coface_signs
    (K A : SimplicialComplex ℝ (Fin 3 → ℝ)) (hAK : A ≤ K) (hA : A.faces.Finite)
    (R : Set (Fin 3 → ℝ)) (hfront : A.space ⊆ frontier R)
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ),
      C ∈ piecewiseAffineGroupoid (Fin 3 → ℝ) ∧ (K.closedStar p).space ⊆ C.source ∧
      (K.closedStar p).AffineOnFaces C ∧
      (C.source ⊆ R ∨ ∃ (ell : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (n : Fin 3 → ℝ),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ R ↔ 0 ≤ ell (C y))) :
    ∃ (number : (Fin 3 → ℝ) → ℕ) (sign : Finset (Fin 3 → ℝ) → ZMod 2),
      InjOn number A.vertices ∧
      ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
        ∀ s : Finset (Fin 3 → ℝ), s.card = 2 → s ⊆ t → s ⊆ u →
          (sign t + boundaryFaceParity number t s) +
            (sign u + boundaryFaceParity number u s) = 1 := by
  obtain ⟨number, sign, hsign⟩ :=
    exists_standard_frontier_all_edge_signs K A hAK hA R hfront hstars
  exact exists_geometric_coface_signs A number sign hsign

end PoincareConjecture.M76.Dehn
