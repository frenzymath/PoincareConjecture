import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [DecidableEq E]

theorem faceLink_singleton_eq_link (K : SimplicialComplex 𝕜 E) (q : E) :
    K.faceLink {q} = K.link q := by
  ext t
  change (t ∈ K.faces ∧ Disjoint ({q} : Finset E) t ∧ {q} ∪ t ∈ K.faces) ↔
    (t ∈ K.faces ∧ q ∉ t ∧ insert q t ∈ K.faces)
  simp only [Finset.disjoint_singleton_left, Finset.singleton_union]

theorem ncard_faceLink_vertices_eq_cofaces (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    (K.faceLink s).vertices.ncard =
      {t : Finset E | t ∈ K.faces ∧ t.card = s.card + 1 ∧ s ⊆ t}.ncard := by
  apply ncard_congr (fun v _ => insert v s)
  · intro v hv
    have hvs : v ∉ s := (K.faceLink_vertices_subset s hv).2
    refine ⟨?_, by rw [Finset.card_insert_of_notMem hvs], Finset.subset_insert v s⟩
    simpa only [Finset.union_singleton] using hv.2.2
  · intro v w hv _ h
    have hvs : v ∉ s := (K.faceLink_vertices_subset s hv).2
    have hvmem : v ∈ insert w s := h ▸ Finset.mem_insert_self v s
    exact (Finset.mem_insert.mp hvmem).resolve_right hvs
  · rintro t ⟨ht, htc, hst⟩
    have hdiff : (t \ s).card = 1 := by
      rw [Finset.card_sdiff_of_subset hst, htc]
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
    have hvmem : v ∈ t \ s := hv.symm ▸ Finset.mem_singleton_self v
    have hvt := (Finset.mem_sdiff.mp hvmem).1
    have hvs := (Finset.mem_sdiff.mp hvmem).2
    have heq : insert v s = t := by
      rw [← Finset.singleton_union, ← hv, Finset.sdiff_union_of_subset hst]
    refine ⟨v, ?_, heq⟩
    refine ⟨K.down_closed ht (Finset.singleton_subset_iff.mpr hvt)
      (Finset.singleton_nonempty v), Finset.disjoint_singleton_right.mpr hvs, ?_⟩
    simpa only [Finset.union_singleton, heq] using ht

end Geometry.SimplicialComplex
