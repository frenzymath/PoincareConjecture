import PoincareConjecture.Proofs.M76.Mathlib.ProjectedPureCoverage
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFrontierAttachment










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

section Incidence

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]



theorem hasTwoFullCofaces_of_faceLink_ncard_eq_two (K : SimplicialComplex 𝕜 E)
    {s : Finset E} {n : ℕ} (hcard : s.card = n)
    (hlink : (K.faceLink s).vertices.ncard = 2) : K.HasTwoFullCofaces n s := by
  classical
  obtain ⟨p, q, hpq, he⟩ := Set.ncard_eq_two.mp hlink
  have hp : p ∈ (K.faceLink s).vertices := by rw [he]; exact Or.inl rfl
  have hq : q ∈ (K.faceLink s).vertices := by rw [he]; exact Or.inr rfl
  have hps := (K.faceLink_vertices_subset s hp).2
  have hqs := (K.faceLink_vertices_subset s hq).2
  have hpt : insert p s ∈ K.faces := by
    simpa only [Finset.union_singleton] using hp.2.2
  have hqu : insert q s ∈ K.faces := by
    simpa only [Finset.union_singleton] using hq.2.2
  refine ⟨insert p s, hpt, insert q s, hqu,
    Finset.subset_insert p s, Finset.subset_insert q s, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hps, hcard]
  · rw [Finset.card_insert_of_notMem hqs, hcard]
  · intro h
    have hp' : p ∈ insert q s := h ▸ Finset.mem_insert_self p s
    exact (Finset.mem_insert.mp hp').elim hpq hps

end Incidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem subset_of_mem_intrinsicInterior_face (K : SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    {x : E} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxt : x ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  by_contra hsub
  have hproper : s ∩ t ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_left, fun he => hsub (he ▸ Finset.inter_subset_right)⟩
  have hxi : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using
      K.inter_subset_convexHull hs ht ⟨intrinsicInterior_subset hxs, hxt⟩
  have hfront := (K.indep hs).convexHull_subset_intrinsicFrontier hproper hxi
  rw [← intrinsicClosure_sdiff_intrinsicInterior] at hfront
  exact hfront.2 hxs

variable {F : Type*} [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem mem_interior_linearImage_closedFaceStar (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces,
      t ⊆ u ∧ u.card = Module.finrank ℝ F + 1)
    {s : Finset E} (hs : s ∈ K.faces)
    (hpair : ∀ t ∈ K.faces, s ⊆ t → t.card = Module.finrank ℝ F →
      K.HasTwoFullCofaces (Module.finrank ℝ F) t)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (Q : E →L[ℝ] F) (hinj : InjOn Q (K.closedFaceStar s).space) :
    Q x ∈ interior (Q '' (K.closedFaceStar s).space) := by
  classical
  have hpureStar : ∀ t ∈ (K.closedFaceStar s).faces,
      ∃ u ∈ (K.closedFaceStar s).faces, t ⊆ u ∧ u.card = Module.finrank ℝ F + 1 := by
    intro t ht
    obtain ⟨u, hu, hstu, hucard⟩ := hpure (s ∪ t) ht.2
    have hsu : s ⊆ u := Finset.subset_union_left.trans hstu
    have htu : t ⊆ u := Finset.subset_union_right.trans hstu
    refine ⟨u, ⟨hu, ?_⟩, htu, hucard⟩
    simpa only [Finset.union_eq_right.mpr hsu] using hu
  have hsStar : s ∈ (K.closedFaceStar s).faces :=
    ⟨hs, by simpa only [Finset.union_self] using hs⟩
  have hxStar : x ∈ (K.closedFaceStar s).space :=
    convexHull_subset_space hsStar (intrinsicInterior_subset hx)
  apply (K.closedFaceStar s).mem_interior_linearImage_of_paired_facets_at
    (finite_closedFaceStar_faces hfinite s) Q hinj hpureStar hxStar
  intro t ht htcard hxt
  have hst := K.subset_of_mem_intrinsicInterior_face hs ht.1 hx hxt
  obtain ⟨u, hu, v, hv, htu, htv, hucard, hvcard, huv⟩ := hpair t ht.1 hst htcard
  refine ⟨u, ⟨hu, ?_⟩, v, ⟨hv, ?_⟩, htu, htv, hucard, hvcard, huv⟩
  · simpa only [Finset.union_eq_right.mpr (hst.trans htu)] using hu
  · simpa only [Finset.union_eq_right.mpr (hst.trans htv)] using hv

end Geometry.SimplicialComplex
