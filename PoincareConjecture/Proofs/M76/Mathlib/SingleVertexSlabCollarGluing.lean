import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexSlabCommonEdge
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

theorem exists_singleVertexSlab_collar_iUnion (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0) {β : ℝ} (hβ : 0 ≤ β)
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    (s : ι → Finset E) (hs : ∀ i, s i ∈ K.faces) (hcard : ∀ i, (s i).card = 3)
    (hinj : Function.Injective s) (S : ι → Set (E × ℝ)) (T : ι → Set E)
    (H : ∀ i, S i ≃ₜ T i) (hH : ∀ i, (H i).IsFinitePL)
    (hsource : ∀ i (p : S i), (p : E × ℝ).1 ∈ convexHull ℝ (s i : Set E))
    (hzero : ∀ i (p : S i), A (p : E × ℝ).1 = 0)
    (hbound : ∀ i (p : S i), (p : E × ℝ).2 ∈ Icc 0 β)
    (htarget : ∀ i, T i ⊆ convexHull ℝ (s i : Set E))
    (hheight : ∀ i (p : S i), A (H i p) = (p : E × ℝ).2)
    (hbottom : ∀ i (p : S i), (p : E × ℝ).2 = 0 → (H i p : E) = (p : E × ℝ).1)
    (hcollapse : ∀ i (p : S i), (p : E × ℝ).1 = q → (p : E × ℝ).2 = 0)
    (hedge : ∀ i (e : Finset E), e.card = 2 → e ⊆ s i → ∀ p : S i,
      (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔ (H i p : E) ∈ convexHull ℝ (e : Set E)) :
    ∃ G : (⋃ i, S i) ≃ₜ (⋃ i, T i), G.IsFinitePL ∧
      (∀ p, A (G p) = (p : E × ℝ).2) ∧
      (∀ p : (⋃ i, S i), (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
      ∀ i (p : S i), (G ⟨p, mem_iUnion.mpr ⟨i, p.property⟩⟩ : E) = H i p := by
  have hagree : ∀ i j (p : E × ℝ) (hi : p ∈ S i) (hj : p ∈ S j),
      (H i ⟨p, hi⟩ : E) = H j ⟨p, hj⟩ := by
    intro i j p hi hj
    by_cases hij : i = j
    · subst j
      rfl
    by_cases hpq : p.1 = q
    · have ht0 := hcollapse i ⟨p, hi⟩ hpq
      exact (hbottom i ⟨p, hi⟩ ht0).trans (hbottom j ⟨p, hj⟩ ht0).symm
    have hA : A p.1 ∈ Icc 0 β := by
      rw [hzero i ⟨p, hi⟩]
      exact ⟨le_rfl, hβ⟩
    obtain ⟨e, he, _, hei, hej, hpe, hAe⟩ :=
      K.common_edge_of_singleVertexSlab_intersection A hreg (hs i) (hs j)
        (hcard i) (hcard j) (fun h => hij (hinj h))
        (hsource i ⟨p, hi⟩) (hsource j ⟨p, hj⟩) hA hpq
    exact hAe ((hedge i e he hei ⟨p, hi⟩).mp hpe) ((hedge j e he hej ⟨p, hj⟩).mp hpe)
      ((hheight i ⟨p, hi⟩).trans (hheight j ⟨p, hj⟩).symm)
  have hoverlap : ∀ i j (p : S i), (p : E × ℝ) ∈ S j ↔ (H i p : E) ∈ T j := by
    intro i j p
    by_cases hij : i = j
    · subst j
      exact iff_of_true p.property (H i p).property
    constructor
    · intro hpj
      rw [hagree i j p p.property hpj]
      exact (H j ⟨p, hpj⟩).property
    · intro hxj
      let z : S j := (H j).symm ⟨H i p, hxj⟩
      have hz : (H j z : E) = H i p := congrArg Subtype.val ((H j).apply_symm_apply _)
      have ht : (z : E × ℝ).2 = (p : E × ℝ).2 :=
        (hheight j z).symm.trans ((congrArg A hz).trans (hheight i p))
      have hbase : (z : E × ℝ).1 = (p : E × ℝ).1 := by
        by_cases hxq : (H i p : E) = q
        · have ht0 : (p : E × ℝ).2 = 0 :=
            (hheight i p).symm.trans ((congrArg A hxq).trans hAq)
          exact (hbottom j z (ht.trans ht0)).symm.trans (hz.trans (hbottom i p ht0))
        have hxA : A (H i p) ∈ Icc 0 β := by
          rw [hheight]
          exact hbound i p
        obtain ⟨e, he, _, hei, hej, hxe, hAe⟩ :=
          K.common_edge_of_singleVertexSlab_intersection A hreg (hs i) (hs j)
            (hcard i) (hcard j) (fun h => hij (hinj h))
            (htarget i (H i p).property) (htarget j hxj) hxA hxq
        have hze : (z : E × ℝ).1 ∈ convexHull ℝ (e : Set E) :=
          (hedge j e he hej z).mpr (by rw [hz]; exact hxe)
        have hpe : (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) :=
          (hedge i e he hei p).mpr hxe
        exact hAe hze hpe ((hzero j z).trans (hzero i p).symm)
      have hzp : (z : E × ℝ) = (p : E × ℝ) := Prod.ext hbase ht
      exact hzp ▸ z.property
  obtain ⟨G, hG, hres⟩ := Homeomorph.exists_iUnion_finitePL S T H hH hoverlap hagree
  refine ⟨G, hG, ?_, ?_, hres⟩
  · intro p
    obtain ⟨i, hi⟩ := mem_iUnion.mp p.property
    have hp : (G p : E) = H i ⟨p, hi⟩ := hres i ⟨p, hi⟩
    rw [hp]
    exact hheight i ⟨p, hi⟩
  · intro p ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp p.property
    have hp : (G p : E) = H i ⟨p, hi⟩ := hres i ⟨p, hi⟩
    rw [hp]
    exact hbottom i ⟨p, hi⟩ ht

end Geometry.SimplicialComplex
