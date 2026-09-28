import PoincareConjecture.Proofs.M76.Mathlib.RadialConeCarriers










set_option autoImplicit false

open Set

namespace AbstractSimplicialComplex

variable {ι κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι} {B : AbstractSimplicialComplex κ}




theorem RadialEmbedding.complex_eq_of_reindex (v : A.RadialEmbedding E)
    (w : B.RadialEmbedding E) (e : κ ≃ ι)
    (hfaces : ∀ s : Finset κ, s ∈ B.faces ↔ s.map e.toEmbedding ∈ A.faces)
    (hvertices : ∀ i, w.val i = v.val (e i)) : w.complex = v.complex := by
  classical
  have himage : ∀ s : Finset κ, w.val '' (s : Set κ) =
      v.val '' (s.map e.toEmbedding : Set ι) := by
    intro s
    simp only [Finset.coe_map, image_image, Equiv.coe_toEmbedding, ← hvertices]
  ext t
  rw [w.complex_faces, v.complex_faces]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s.map e.toEmbedding, (hfaces s).mp hs, ht.trans (himage s)⟩
  · rintro ⟨s, hs, ht⟩
    obtain ⟨r, hr⟩ := e.finsetCongr.surjective s
    have hr' : r.map e.toEmbedding = s := hr
    refine ⟨r, (hfaces r).mpr (hr'.symm ▸ hs), ?_⟩
    exact ht.trans (hr' ▸ (himage r).symm)




theorem RadialEmbedding.cone_eq_of_reindex (v : A.RadialEmbedding E)
    (w : B.RadialEmbedding E) (e : κ ≃ ι)
    (hfaces : ∀ s : Finset κ, s ∈ B.faces ↔ s.map e.toEmbedding ∈ A.faces)
    (hvertices : ∀ i, w.val i = v.val (e i)) : w.cone = v.cone := by
  classical
  have he := v.complex_eq_of_reindex w e hfaces hvertices
  ext t
  change (t.Nonempty ∧ (t.erase 0 = ∅ ∨ t.erase 0 ∈ w.complex.faces)) ↔
    (t.Nonempty ∧ (t.erase 0 = ∅ ∨ t.erase 0 ∈ v.complex.faces))
  rw [he]




theorem RadialEmbedding.subtype_basis_span_cone_space (v : A.RadialEmbedding E)
    (hv : LinearIndependent ℝ v.val) :
    (Submodule.span ℝ (range v.val)).subtype ''
      (A.basisRadialEmbedding (Module.Basis.span hv)).cone.space = v.cone.space := by
  let V := Submodule.span ℝ (range v.val)
  let b : Module.Basis ι ℝ V := Module.Basis.span hv
  have hb : (fun i => V.subtype (b i)) = v.val :=
    funext (fun i => Module.Basis.coe_span_apply hv i)
  change V.subtype '' (A.basisRadialEmbedding b).cone.space = v.cone.space
  simp only [RadialEmbedding.cone_space, image_iUnion, V.subtype.image_convexHull,
    image_insert_eq, map_zero, image_image, basisRadialEmbedding, hb]

end AbstractSimplicialComplex
