import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators
import Mathlib.Analysis.LocallyConvex.Separation









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



def frontierSubcomplex (K : SimplicialComplex ℝ E) (s : Set E) :
    SimplicialComplex ℝ E where
  faces := {t | t ∈ K.faces ∧ convexHull ℝ (t : Set E) ⊆ frontier s}
  indep ht := K.indep ht.1
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨K.nonempty_of_mem_faces ht.1, ?_⟩
    intro r hrt hr
    exact ⟨K.down_closed ht.1 hrt hr, (convexHull_mono hrt).trans ht.2⟩
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1



theorem frontierSubcomplex_finite (K : SimplicialComplex ℝ E) (s : Set E)
    (hK : K.faces.Finite) : (K.frontierSubcomplex s).faces.Finite :=
  hK.subset (fun _ ht => ht.1)




theorem frontierSubcomplex_space (K : SimplicialComplex ℝ E) {s : Set E}
    (hs : IsClosed s) (hcv : Convex ℝ s) (hne : (interior s).Nonempty)
    (hspace : K.space = s) : (K.frontierSubcomplex s).space = frontier s := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    exact ht.2 hxt
  · intro x hx
    obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hcv.interior isOpen_interior hx.2
    have hle : ∀ y ∈ s, L y ≤ L x := by
      intro y hy
      apply le_on_closure (fun z hz => (hL z hz).le)
        L.continuous.continuousOn continuousOn_const
      rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne, hs.closure_eq]
      exact hy
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp (hspace.symm ▸ hs.frontier_subset hx)
    let A : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E (L x) - L.toLinearMap.toAffineMap
    let r := t.filter (fun v => A v = 0)
    have hxr : x ∈ convexHull ℝ (r : Set E) := by
      have hr : (r : Set E) = (t : Set E) ∩ {v | A v = 0} := by
        ext v
        simp only [r, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
      rw [hr]
      apply t.mem_convexHull_zero_vertices A
      · intro v hv
        exact sub_nonneg.mpr (hle v (hspace ▸ K.subset_space ht hv))
      · exact hxt
      · change L x - L x = 0
        exact sub_self _
    have hrne := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxr⟩)
    have hrK := K.down_closed ht (Finset.filter_subset _ _) hrne
    refine mem_space_iff.mpr ⟨r, ⟨hrK, ?_⟩, hxr⟩
    intro y hy
    have hAy : A y = 0 :=
      (AffineMap.eqOn_affineSpan (f := A) (g := AffineMap.const ℝ E 0)
        (fun v hv => (Finset.mem_filter.mp hv).2)) (convexHull_subset_affineSpan _ hy)
    have hyS : y ∈ s := hspace ▸ K.convexHull_subset_space hrK hy
    refine ⟨subset_closure hyS, fun hyi => ?_⟩
    have hlt := hL y hyi
    change L x - L y = 0 at hAy
    linarith

end Geometry.SimplicialComplex
