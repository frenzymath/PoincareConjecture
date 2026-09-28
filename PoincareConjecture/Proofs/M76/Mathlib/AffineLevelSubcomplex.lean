import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineZeroSubcomplex (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∀ x ∈ s, A x = 0}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, fun x hx => hs.2 x (hts hx)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem affineZeroSubcomplex_finite (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) :
    (K.affineZeroSubcomplex A).faces.Finite := hK.subset (fun _ hs => hs.1)

theorem affineZeroSubcomplex_space (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hA : K.RespectsAffineHyperplane A) :
    (K.affineZeroSubcomplex A).space = K.space ∩ {x | A x = 0} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    refine ⟨mem_space_iff.mpr ⟨s, hs.1, hxs⟩, ?_⟩
    exact (AffineMap.eqOn_affineSpan
      (f := A) (g := AffineMap.const ℝ E 0) (fun v hv => hs.2 v hv))
      (convexHull_subset_affineSpan _ hxs)
  · rintro ⟨hx, hAx⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    let t := s.filter (fun v => A v = 0)
    have hxt : x ∈ convexHull ℝ (t : Set E) := by
      have ht : (t : Set E) = (s : Set E) ∩ {v | A v = 0} := by
        ext v
        simp only [t, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
      rw [ht]
      rcases hA s hs with hneg | hpos
      · have h := s.mem_convexHull_zero_vertices (-A)
          (fun v hv => neg_nonneg.mpr (hneg v (subset_convexHull ℝ _ hv))) hxs
          (by change -A x = 0; rw [hAx, neg_zero])
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using h
      · exact s.mem_convexHull_zero_vertices A
          (fun v hv => hpos v (subset_convexHull ℝ _ hv)) hxs hAx
    have htne := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    exact mem_space_iff.mpr ⟨t,
      ⟨K.down_closed hs (Finset.filter_subset _ _) htne,
        fun v hv => (Finset.mem_filter.mp hv).2⟩, hxt⟩

end Geometry.SimplicialComplex
