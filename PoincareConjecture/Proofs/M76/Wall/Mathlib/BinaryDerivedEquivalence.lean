import PoincareConjecture.Proofs.M76.Wall.Mathlib.PositiveDerivedRestriction
import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryFaceCenters
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSubdivision

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem exists_binaryDerived_homeomorph (A : SimplicialComplex ℝ E) (hAK : A ≤ K) :
    ∃ (f g : E → E) (e : K.space ≃ₜ K.space),
      K.barycentricSubdivision.AffineOnFaces f ∧
      (K.derivedSubdivision (fun s => s.val.binaryFaceCenter A.vertices)
        (K.positive_binary_face_centers A.vertices)).AffineOnFaces g ∧
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧
      (∀ s : K.faces, f (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices) ∧
      (∀ s : K.faces, g (s.val.binaryFaceCenter A.vertices) = s.val.centroid ℝ id) ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      (∀ x : K.space, (e.symm x : E) = g x) ∧
      (∀ L : SimplicialComplex ℝ E, L ≤ K →
        f '' L.space = L.space ∧ g '' L.space = L.space) ∧ EqOn f id A.space := by
  classical
  let c : K.faces → E := fun s => s.val.centroid ℝ id
  have hc (s : K.faces) : ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
      (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s := by
    have hs := K.nonempty_of_mem_faces s.property
    refine ⟨s.val.centroidWeights ℝ, ?_,
      s.val.sum_centroidWeights_eq_one_of_nonempty ℝ hs, ?_⟩
    · intro v _
      simp only [Finset.centroidWeights_apply, inv_pos]
      exact_mod_cast hs.card_pos
    · change (∑ v ∈ s.val, s.val.centroidWeights ℝ v • v) = s.val.centroid ℝ id
      rw [Finset.centroid_eq_inv_card_smul_sum _ hs]
      simp only [Finset.centroidWeights_apply, Finset.smul_sum, id_eq]
  let d : K.faces → E := fun s => s.val.binaryFaceCenter A.vertices
  have hd := K.positive_binary_face_centers A.vertices
  obtain ⟨f, g, e, hf, hg, he, hei, hfc, hgd, hval, hinv⟩ :=
    K.exists_positiveDerived_homeomorph c d hc hd
  have hfg : RightInvOn g f K.space := by
    intro x hx
    calc
      f (g x) = f (e.symm ⟨x, hx⟩) := congrArg f (hinv ⟨x, hx⟩).symm
      _ = (e (e.symm ⟨x, hx⟩) : E) := (hval (e.symm ⟨x, hx⟩)).symm
      _ = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hgf : RightInvOn f g K.space := by
    intro x hx
    calc
      g (f x) = g (e ⟨x, hx⟩) := congrArg g (hval ⟨x, hx⟩).symm
      _ = (e.symm (e ⟨x, hx⟩) : E) := (hinv (e ⟨x, hx⟩)).symm
      _ = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  have hfB : K.barycentricSubdivision.AffineOnFaces f := hf
  refine ⟨f, g, e, hfB, hg, he, hei, hfc, hgd, hval, hinv, ?_, ?_⟩
  · intro L hLK
    exact ⟨K.positiveDerived_image_subcomplex c hc d hd hf hg hfc hgd hfg hLK,
      K.positiveDerived_image_subcomplex d hd c hc hg hf hgd hfc hgf hLK⟩
  · apply K.positiveDerived_eqOn_subcomplex c hc hf hAK
    intro s
    exact (hfc ⟨s.val, hAK s.property⟩).trans
      (s.val.binaryFaceCenter_eq_centroid (A.nonempty_of_mem_faces s.property) A.vertices
        (Or.inl (fun v hv => A.down_closed s.property
          (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))))

end Geometry.SimplicialComplex
