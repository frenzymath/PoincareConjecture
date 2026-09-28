import PoincareConjecture.Proofs.M76.Mathlib.DerivedFaceChainIncidence
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph











set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c d : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)
  (hd : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = d s)





theorem exists_positiveDerived_homeomorph :
    ∃ (f g : E → E) (e : K.space ≃ₜ K.space),
      (K.derivedSubdivision c hc).AffineOnFaces f ∧
      (K.derivedSubdivision d hd).AffineOnFaces g ∧
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧
      (∀ s : K.faces, f (c s) = d s) ∧
      (∀ s : K.faces, g (d s) = c s) ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      (∀ x : K.space, (e.symm x : E) = g x) := by
  classical
  let C := K.derivedSubdivision c hc
  let D := K.derivedSubdivision d hd
  let v : E → E := Function.extend c d (fun _ => 0)
  let w : E → E := Function.extend d c (fun _ => 0)
  have hv (s : K.faces) : v (c s) = d s :=
    (K.positiveFaceCenter_injective c hc).extend_apply d _ s
  have hw (s : K.faces) : w (d s) = c s :=
    (K.positiveFaceCenter_injective d hd).extend_apply c _ s
  have hCv : C.vertices = range c := K.derivedSubdivision_vertices_eq_range c hc
  have hDv : D.vertices = range d := K.derivedSubdivision_vertices_eq_range d hd
  have hvfaces : ∀ s ∈ C.faces, ∃ t ∈ D.faces,
      v '' (s : Set E) ⊆ (t : Set E) := by
    intro s hs
    obtain ⟨a, ha, hchain, rfl⟩ := (K.derivedSubdivision_faces c hc s).mp hs
    refine ⟨a.image d, (K.derivedSubdivision_faces d hd _).mpr
      ⟨a, ha, hchain, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, hi, (hv i).symm⟩
  have hwfaces : ∀ s ∈ D.faces, ∃ t ∈ C.faces,
      w '' (s : Set E) ⊆ (t : Set E) := by
    intro s hs
    obtain ⟨a, ha, hchain, rfl⟩ := (K.derivedSubdivision_faces d hd s).mp hs
    refine ⟨a.image c, (K.derivedSubdivision_faces c hc _).mpr
      ⟨a, ha, hchain, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, hi, (hw i).symm⟩
  have hleft : LeftInvOn w v C.vertices := by
    intro x hx
    obtain ⟨i, rfl⟩ := hCv.subset hx
    rw [hv, hw]
  have hright : RightInvOn w v D.vertices := by
    intro x hx
    obtain ⟨i, rfl⟩ := hDv.subset hx
    rw [hw, hv]
  obtain ⟨f, g, H, hf, hg, hfv, hgw, hH, hHi⟩ :=
    C.exists_homeomorph_of_vertex_maps D (K.derivedSubdivision_finite c hc)
      v w hvfaces hwfaces hleft hright
  have hC : C.space = K.space := K.derivedSubdivision_space c hc
  have hD : D.space = K.space := K.derivedSubdivision_space d hd
  let e : K.space ≃ₜ K.space :=
    (Homeomorph.setCongr hC.symm).trans (H.trans (Homeomorph.setCongr hD))
  have he (x : K.space) : (e x : E) = f x :=
    hH ⟨x, hC.symm ▸ x.property⟩
  have hei (x : K.space) : (e.symm x : E) = g x :=
    hHi ⟨x, hD.symm ▸ x.property⟩
  refine ⟨f, g, e, hf, hg,
    ⟨f, ⟨C, K.derivedSubdivision_finite c hc, hC, hf⟩, he⟩,
    ⟨g, ⟨D, K.derivedSubdivision_finite d hd, hD, hg⟩, hei⟩,
    ?_, ?_, he, hei⟩
  · intro s
    exact (hfv (hCv.superset ⟨s, rfl⟩)).trans (hv s)
  · intro s
    exact (hgw (hDv.superset ⟨s, rfl⟩)).trans (hw s)

end Geometry.SimplicialComplex
