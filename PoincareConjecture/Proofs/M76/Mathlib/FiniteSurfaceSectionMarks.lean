import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem subsingleton_segment_inter_level (A : E →ᵃ[ℝ] ℝ)
    {a b : E} (hab : A a ≠ A b) (c : ℝ) :
    (segment ℝ a b ∩ {x | A x = c}).Subsingleton := by
  rintro x ⟨hx, hxc⟩ y ⟨hy, hyc⟩
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨u, _, rfl⟩ := hx
  obtain ⟨v, _, rfl⟩ := hy
  have huv : lineMap (A a) (A b) u = lineMap (A a) (A b) v := by
    simpa only [A.apply_lineMap] using hxc.trans hyc.symm
  exact congrArg (lineMap a b) (lineMap_injective ℝ hab huv)

end AffineMap

namespace Geometry.SimplicialComplex

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def oneSkeletonHeightSection (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (c : ℝ) : Set E :=
  {x | ∃ s ∈ K.faces, s.card ≤ 2 ∧
    x ∈ convexHull ℝ (s : Set E) ∧ A x = c}

theorem oneSkeletonHeightSection_subset (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (c : ℝ) :
    K.oneSkeletonHeightSection A c ⊆ K.space ∩ {x | A x = c} := by
  rintro x ⟨s, hs, _, hxs, hxc⟩
  exact ⟨K.convexHull_subset_space hs hxs, hxc⟩

theorem subsingleton_small_face_height_section (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    {s : Finset E} (hs : s ∈ K.faces) (hsc : s.card ≤ 2) (c : ℝ) :
    (convexHull ℝ (s : Set E) ∩ {x | A x = c}).Subsingleton := by
  classical
  have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hsingle | hedge
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsingle
    simp only [Finset.coe_singleton, convexHull_singleton]
    intro x hx y hy
    exact Set.subsingleton_singleton hx.1 hy.1
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hedge
    have ha : a ∈ K.vertices := K.down_closed hs
      (by simp) (Finset.singleton_nonempty a)
    have hb : b ∈ K.vertices := K.down_closed hs
      (by simp) (Finset.singleton_nonempty b)
    have hheight : A a ≠ A b := fun h => hab (hA ha hb h)
    simpa only [Finset.coe_pair, convexHull_pair] using
      A.subsingleton_segment_inter_level hheight c

theorem finite_oneSkeletonHeightSection (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ)
    (hA : InjOn A K.vertices) (c : ℝ) :
    (K.oneSkeletonHeightSection A c).Finite := by
  have hsmall : {s : Finset E | s ∈ K.faces ∧ s.card ≤ 2}.Finite :=
    hK.subset fun _ hs => hs.1
  have hunion := hsmall.biUnion (fun s hs =>
    (K.subsingleton_small_face_height_section A hA hs.1 hs.2 c).finite)
  apply hunion.subset
  rintro x ⟨s, hs, hsc, hxs, hxc⟩
  exact mem_iUnion₂.mpr ⟨s, ⟨hs, hsc⟩, hxs, hxc⟩

end Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_triangle_intrinsicInterior_of_notMem_oneSkeletonHeightSection
    (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {c : ℝ} {x : E}
    (hx : x ∈ K.space ∩ {x | A x = c})
    (hmark : x ∉ K.oneSkeletonHeightSection A c) :
    ∃ t ∈ K.faces, t.card = 3 ∧
      x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
  obtain ⟨t, ht, htc, hst⟩ := hpure s hs
  have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hst hxs
  refine ⟨t, ht, htc, ?_⟩
  by_contra hnot
  have hfront : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hxt, hnot⟩
  obtain ⟨v, hvt, hxv⟩ :=
    (AffineIndependent.mem_intrinsicFrontier_convexHull_finset
      (K.nonempty_of_mem_faces ht) (K.indep ht) x).mp hfront
  have hcard : (t.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvt, htc]
  have hface : t.erase v ∈ K.faces := K.down_closed ht
    (Finset.erase_subset v t) (Finset.card_pos.mp (by omega))
  exact hmark ⟨t.erase v, hface, hcard.le, hxv, hx.2⟩

theorem exists_finite_height_section_triangle_interiors
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) (c : ℝ) :
    ∃ F : Set E, F = K.oneSkeletonHeightSection A c ∧ F.Finite ∧
      F ⊆ K.space ∩ {x | A x = c} ∧
      ∀ x ∈ (K.space ∩ {x | A x = c}) \ F,
        ∃ t ∈ K.faces, t.card = 3 ∧
          x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) := by
  refine ⟨K.oneSkeletonHeightSection A c, rfl,
    K.finite_oneSkeletonHeightSection hK A hA c,
    K.oneSkeletonHeightSection_subset A c, ?_⟩
  intro x hx
  exact K.exists_triangle_intrinsicInterior_of_notMem_oneSkeletonHeightSection
    hpure A hx.1 hx.2

end Geometry.SimplicialComplex
