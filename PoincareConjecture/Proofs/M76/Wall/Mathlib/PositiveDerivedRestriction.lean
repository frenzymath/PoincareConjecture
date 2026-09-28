import PoincareConjecture.Proofs.M76.Wall.Mathlib.PositiveDerivedEquivalence
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)



theorem derivedSubdivision_mono_face_labels
    {L : SimplicialComplex ℝ E} [Fintype L.faces] (hLK : L ≤ K) :
    L.derivedSubdivision (fun s => c ⟨s.val, hLK s.property⟩)
      (fun s => hc ⟨s.val, hLK s.property⟩) ≤ K.derivedSubdivision c hc := by
  classical
  let i : L.faces → K.faces := fun s => ⟨s.val, hLK s.property⟩
  intro t ht
  obtain ⟨a, ha, hchain, rfl⟩ :=
    (L.derivedSubdivision_faces (fun s => c (i s)) (fun s => hc (i s)) t).mp ht
  apply (K.derivedSubdivision_faces c hc _).mpr
  refine ⟨a.image i, ha.image i, ?_, ?_⟩
  · intro s hs t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    exact hchain u hu v hv
  · rw [Finset.image_image]
    rfl

variable (d : K.faces → E)
  (hd : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = d s)

include hd in



theorem positiveDerived_mapsTo_subcomplex {f : E → E}
    (hf : (K.derivedSubdivision c hc).AffineOnFaces f)
    (hcenters : ∀ s : K.faces, f (c s) = d s)
    {L : SimplicialComplex ℝ E} (hLK : L ≤ K) : MapsTo f L.space L.space := by
  classical
  let : Fintype L.faces := ((Set.toFinite K.faces).subset (fun _ hs => hLK hs)).fintype
  let i : L.faces → K.faces := fun s => ⟨s.val, hLK s.property⟩
  let C := L.derivedSubdivision (fun s => c (i s)) (fun s => hc (i s))
  let D := L.derivedSubdivision (fun s => d (i s)) (fun s => hd (i s))
  have hC : C ≤ K.derivedSubdivision c hc :=
    K.derivedSubdivision_mono_face_labels c hc hLK
  have hfC : C.AffineOnFaces f :=
    hf.of_face_containment (fun s hs => ⟨s, hC hs, Subset.rfl⟩)
  have hfaces : ∀ s ∈ C.faces, ∃ t ∈ D.faces,
      f '' (s : Set E) ⊆ (t : Set E) := by
    intro s hs
    obtain ⟨a, ha, hchain, rfl⟩ :=
      (L.derivedSubdivision_faces (fun s => c (i s)) (fun s => hc (i s)) s).mp hs
    refine ⟨a.image (fun s => d (i s)),
      (L.derivedSubdivision_faces (fun s => d (i s)) (fun s => hd (i s)) _).mpr
        ⟨a, ha, hchain, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨s, hs, (hcenters (i s)).symm⟩
  have hCs : C.space = L.space :=
    L.derivedSubdivision_space (fun s => c (i s)) (fun s => hc (i s))
  have hDs : D.space = L.space :=
    L.derivedSubdivision_space (fun s => d (i s)) (fun s => hd (i s))
  intro x hx
  have hxC : x ∈ C.space := hCs.symm ▸ hx
  exact hDs ▸ hfC.mapsTo_space hfaces hxC




theorem positiveDerived_image_subcomplex {f g : E → E}
    (hf : (K.derivedSubdivision c hc).AffineOnFaces f)
    (hg : (K.derivedSubdivision d hd).AffineOnFaces g)
    (hfc : ∀ s : K.faces, f (c s) = d s)
    (hgd : ∀ s : K.faces, g (d s) = c s)
    (hfg : RightInvOn g f K.space)
    {L : SimplicialComplex ℝ E} (hLK : L ≤ K) : f '' L.space = L.space := by
  have hmapf := K.positiveDerived_mapsTo_subcomplex c hc d hd hf hfc hLK
  have hmapg := K.positiveDerived_mapsTo_subcomplex d hd c hc hg hgd hLK
  apply Subset.antisymm hmapf.image_subset
  intro x hx
  exact ⟨g x, hmapg hx, hfg (space_subset_of_le hLK hx)⟩




theorem positiveDerived_image_convexHull {f g : E → E}
    (hf : (K.derivedSubdivision c hc).AffineOnFaces f)
    (hg : (K.derivedSubdivision d hd).AffineOnFaces g)
    (hfc : ∀ s : K.faces, f (c s) = d s)
    (hgd : ∀ s : K.faces, g (d s) = c s)
    (hfg : RightInvOn g f K.space) (s : K.faces) :
    f '' convexHull ℝ (s.val : Set E) = convexHull ℝ (s.val : Set E) := by
  classical
  let L := K.finiteFaceSpan {s}
  have hL : L.space = convexHull ℝ (s.val : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
      obtain ⟨_, u, hu, htu⟩ := (K.finiteFaceSpan_faces {s} t).mp ht
      have hus : u = s := Finset.mem_singleton.mp hu
      subst u
      exact convexHull_mono htu hxt
    · intro hx
      apply L.convexHull_subset_space (s := s.val) _ hx
      exact (K.finiteFaceSpan_faces {s} s.val).mpr
        ⟨K.nonempty_of_mem_faces s.property, s, Finset.mem_singleton_self s, Subset.rfl⟩
  rw [← hL]
  exact K.positiveDerived_image_subcomplex c hc d hd hf hg hfc hgd hfg
    (K.finiteFaceSpan_le {s})




theorem positiveDerived_eqOn_subcomplex {f : E → E}
    (hf : (K.derivedSubdivision c hc).AffineOnFaces f)
    {L : SimplicialComplex ℝ E} (hLK : L ≤ K)
    (hfix : ∀ s : L.faces, f (c ⟨s.val, hLK s.property⟩) = c ⟨s.val, hLK s.property⟩) :
    EqOn f id L.space := by
  classical
  let : Fintype L.faces := ((Set.toFinite K.faces).subset (fun _ hs => hLK hs)).fintype
  let i : L.faces → K.faces := fun s => ⟨s.val, hLK s.property⟩
  let C := L.derivedSubdivision (fun s => c (i s)) (fun s => hc (i s))
  have hC : C ≤ K.derivedSubdivision c hc :=
    K.derivedSubdivision_mono_face_labels c hc hLK
  have hfC : C.AffineOnFaces f :=
    hf.of_face_containment (fun s hs => ⟨s, hC hs, Subset.rfl⟩)
  have heq : EqOn f id C.space :=
    hfC.eqOn_of_eqOn_vertices (C.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)) (by
      intro x hx
      obtain ⟨s, rfl⟩ :=
        (L.derivedSubdivision_vertices_eq_range (fun s => c (i s))
          (fun s => hc (i s))).subset hx
      exact hfix s)
  have hCs : C.space = L.space :=
    L.derivedSubdivision_space (fun s => c (i s)) (fun s => hc (i s))
  rwa [hCs] at heq

end Geometry.SimplicialComplex
