import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SimplicialComplex.Basic










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {F : Set (Finset E)}

private theorem subface_inter_subset
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T))
    {s t S T : Finset E} (hS : S ∈ F) (hs : s ⊆ S) (hT : T ∈ F) (ht : t ⊆ T) :
    convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 (t : Set E) ⊆
      convexHull 𝕜 ((s : Set E) ∩ t) := by
  classical
  rintro x ⟨hxs, hxt⟩
  have hxST := hinter S hS T hT ⟨convexHull_mono hs hxs, convexHull_mono ht hxt⟩
  have hxsST : x ∈ convexHull 𝕜 (s ∩ (S ∩ T) : Set E) := by
    have he := (hind S hS).convexHull_inter hs (t₂ := S ∩ T) Finset.inter_subset_left
    simp only [Finset.coe_inter] at he
    rw [he]
    exact ⟨hxs, hxST⟩
  have hxsT : s ∩ (S ∩ T) ⊆ T :=
    Finset.inter_subset_right.trans Finset.inter_subset_right
  have hxst : x ∈ convexHull 𝕜 ((s ∩ (S ∩ T)) ∩ t : Set E) := by
    have he := (hind T hT).convexHull_inter hxsT ht
    simp only [Finset.coe_inter] at he
    rw [he]
    exact ⟨hxsST, hxt⟩
  have hsub : ((s : Set E) ∩ ((S : Set E) ∩ T)) ∩ t ⊆ (s : Set E) ∩ t :=
    fun _ hx => ⟨hx.1.1, hx.2⟩
  exact convexHull_mono hsub hxst




def ofGenerators (F : Set (Finset E))
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) : SimplicialComplex 𝕜 E where
  faces := {s | s.Nonempty ∧ ∃ S ∈ F, s ⊆ S}
  isRelLowerSet_faces := by
    rintro s ⟨hs, S, hS, hsS⟩
    exact ⟨hs, fun t hts ht => ⟨ht, S, hS, hts.trans hsS⟩⟩
  indep := by
    rintro s ⟨_, S, hS, hsS⟩
    exact (hind S hS).mono hsS
  inter_subset_convexHull := by
    rintro s t ⟨_, S, hS, hsS⟩ ⟨_, T, hT, htT⟩
    exact subface_inter_subset hind hinter hS hsS hT htT



theorem mem_ofGenerators_faces
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) (s : Finset E) :
    s ∈ (ofGenerators F hind hinter).faces ↔ s.Nonempty ∧ ∃ S ∈ F, s ⊆ S := Iff.rfl




theorem space_ofGenerators
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) :
    (ofGenerators F hind hinter).space = ⋃ S ∈ F, convexHull 𝕜 (S : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨_, S, hS, hsS⟩, hxs⟩ := mem_space_iff.mp hx
    exact mem_iUnion₂.mpr ⟨S, hS, convexHull_mono hsS hxs⟩
  · intro hx
    obtain ⟨S, hS, hxS⟩ := mem_iUnion₂.mp hx
    have hne : S.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty,
        convexHull_empty, notMem_empty] at hxS
    exact mem_space_iff.mpr ⟨S, ⟨hne, S, hS, Finset.Subset.refl _⟩, hxS⟩



theorem finite_ofGenerators_faces (hF : F.Finite)
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) :
    (ofGenerators F hind hinter).faces.Finite := by
  classical
  apply (hF.biUnion (fun S _ => S.powerset.finite_toSet)).subset
  rintro s ⟨_, S, hS, hsS⟩
  exact mem_iUnion₂.mpr ⟨S, hS, Finset.mem_powerset.mpr hsS⟩

end Geometry.SimplicialComplex
