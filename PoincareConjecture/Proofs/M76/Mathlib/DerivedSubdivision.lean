import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedLinearImage
import PoincareConjecture.Proofs.M02.Topology.GeometricFlags
import PoincareConjecture.Proofs.M02.Topology.GeometricAffineFlags









set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

open PoincareConjecture.Proofs.M02.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

include hc in
private theorem faceCenterMap_injOn :
    InjOn (Fintype.linearCombination ℝ c).toContinuousLinearMap
      (finiteOrderComplex K.faces).space := by
  let e := geometricFlagHomeomorphRange K Subtype.val (fun s => s.property)
    (fun _ _ => Iff.rfl) c hc
  intro x hx y hy hxy
  have he : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext hxy
  exact congrArg Subtype.val (e.injective he)



noncomputable def derivedSubdivision : SimplicialComplex ℝ E :=
  (finiteOrderComplex K.faces).embeddedLinearImage
    (Fintype.linearCombination ℝ c).toContinuousLinearMap (K.faceCenterMap_injOn c hc)



theorem derivedSubdivision_faces [DecidableEq E] (t : Finset E) :
    t ∈ (K.derivedSubdivision c hc).faces ↔
      ∃ s : Finset K.faces, s.Nonempty ∧
        (∀ i ∈ s, ∀ j ∈ s, i ≤ j ∨ j ≤ i) ∧ t = s.image c := by
  classical
  rw [derivedSubdivision, embeddedLinearImage_faces]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨s, hs, hchain, rfl⟩ := (finiteOrderComplex_faces K.faces u).mp hu
    refine ⟨s, hs, hchain, ?_⟩
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Fintype.linearCombination_apply_single, one_smul]
  · rintro ⟨s, hs, hchain, rfl⟩
    refine ⟨s.image (fun i => Pi.single i (1 : ℝ)),
      (finiteOrderComplex_faces K.faces _).mpr ⟨s, hs, hchain, ?_⟩, ?_⟩
    · apply Finset.image_congr
      intro i _
      funext j
      by_cases h : j = i <;> simp [h]
    · simp only [Finset.image_image]
      apply Finset.image_congr
      intro i _
      simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
        Fintype.linearCombination_apply_single, one_smul]



theorem derivedSubdivision_finite : (K.derivedSubdivision c hc).faces.Finite := by
  classical
  rw [derivedSubdivision, embeddedLinearImage_faces]
  exact (finiteOrderComplex_finite K.faces).image _



theorem derivedSubdivision_space : (K.derivedSubdivision c hc).space = K.space := by
  classical
  rw [derivedSubdivision, embeddedLinearImage_space]
  have hclosed (s : Finset E) (hs : s ∈ K.faces) (t : Finset E) (hts : t ⊆ s)
      (ht : ∃ x ∈ convexHull ℝ (t : Set E), (0 : E →ᵃ[ℝ] ℝ) x = 0) :
      t ∈ K.faces := by
    obtain ⟨x, hx, _⟩ := ht
    exact K.down_closed hs hts
      (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hx⟩))
  have hcov := geometricAffineFlagMap_range (0 : E →ᵃ[ℝ] ℝ) K.faces
    hclosed c (fun s => ⟨rfl, hc s⟩)
  have himage : (Fintype.linearCombination ℝ c).toContinuousLinearMap ''
      (finiteOrderComplex K.faces).space = range (finiteOrderComplexMap K.faces c) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
  rw [himage, hcov]
  ext x
  constructor
  · rintro ⟨s, hs, _⟩
    exact K.convexHull_subset_space s.property hs
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact ⟨⟨s, hs⟩, hxs, rfl⟩



theorem derivedSubdivision_isSubdivision : (K.derivedSubdivision c hc).IsSubdivision K := by
  classical
  refine ⟨K.derivedSubdivision_space c hc, ?_⟩
  intro t ht
  obtain ⟨s, hs, hchain, rfl⟩ := (K.derivedSubdivision_faces c hc t).mp ht
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal hs
  refine ⟨m.val, m.property, convexHull_min ?_ (convex_convexHull ℝ _)⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have his : i.val ⊆ m.val := by
    rcases hchain i hi m hm with h | h
    · exact h
    · exact hmax hi h
  obtain ⟨w, hw, hsum, hval⟩ := hc i
  exact convexHull_mono his
    (Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩)



theorem derivedSubdivision_card_le {N : ℕ}
    (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) :
    ∀ s ∈ (K.derivedSubdivision c hc).faces, s.card ≤ N + 1 := by
  classical
  intro t ht
  rw [derivedSubdivision, embeddedLinearImage_faces] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have hr : StrictMono (fun i : K.faces => i.val.card) := by
    intro i j hij
    exact Finset.card_lt_card hij
  have hbound := finiteOrderComplex_dimension K.faces (fun i => i.val.card) hr
    1 (N + 1) (fun i => ⟨K.nonempty_of_mem_faces i.property |>.card_pos,
      hN i.val i.property⟩) s hs
  exact (Finset.card_image_le).trans (by omega)

end Geometry.SimplicialComplex
