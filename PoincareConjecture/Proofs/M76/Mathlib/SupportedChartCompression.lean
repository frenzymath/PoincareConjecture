import PoincareConjecture.Proofs.M76.Mathlib.TorusCrossingBandImmersion

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

theorem exists_supported_chart_compression {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    (Q : OpenPartialHomeomorph E X) (H : OpenPartialHomeomorph E E)
    {c : E} {K : Set E} {U : Set X}
    (hK : IsCompact K) (hKS : K ⊆ Q.source) (hcK : c ∈ K)
    (hHS : H.source = Q.source \ {c}) (hHT : H.target ⊆ Q.source)
    (hfix : EqOn H id (Q.source \ K))
    (himage : Q '' H.target ⊆ U) (houtside : (Q '' K)ᶜ ⊆ U) :
    ∃ f : X → X,
      IsLocalHomeomorphOn f {Q c}ᶜ ∧ MapsTo f {Q c}ᶜ U ∧
      EqOn f (Q.symm.trans (H.trans Q)) (Q.symm.trans (H.trans Q)).source ∧
      EqOn f id (Q '' K)ᶜ := by
  have hcS : c ∈ Q.source := hKS hcK
  let e := Q.symm.trans (H.trans Q)
  have hES : e.source = Q.target \ {Q c} := by
    ext z
    change (z ∈ Q.target ∧ Q.symm z ∈ H.source ∧ H (Q.symm z) ∈ Q.source) ↔
      (z ∈ Q.target ∧ z ∉ {Q c})
    constructor
    · rintro ⟨hzQ, hzH, _⟩
      refine ⟨hzQ, ?_⟩
      have hne : Q.symm z ∉ ({c} : Set E) := (hHS ▸ hzH).2
      intro he
      have hz : z = Q c := mem_singleton_iff.mp he
      apply hne
      rw [hz, Q.left_inv hcS]
      exact mem_singleton c
    · rintro ⟨hzQ, hzne⟩
      have hzH : Q.symm z ∈ H.source := by
        rw [hHS]
        refine ⟨Q.map_target hzQ, ?_⟩
        intro he
        apply hzne
        have he' : Q.symm z = c := mem_singleton_iff.mp he
        exact mem_singleton_iff.mpr ((Q.right_inv hzQ).symm.trans (congrArg Q he'))
      exact ⟨hzQ, hzH, hHT (H.map_source hzH)⟩
  have hQK : IsCompact (Q '' K) :=
    hK.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)
  let d : OpenPartialHomeomorph X X := ofSet (Q '' K)ᶜ hQK.isClosed.isOpen_compl
  have hdS : d.source = (Q '' K)ᶜ := rfl
  have hcover : e.source ∪ d.source = {Q c}ᶜ := by
    rw [hES, hdS]
    ext z
    constructor
    · rintro (hz | hz)
      · exact hz.2
      · intro he
        have he' : z = Q c := mem_singleton_iff.mp he
        apply hz
        rw [he']
        exact mem_image_of_mem Q hcK
    · intro hz
      by_cases hzQ : z ∈ Q.target
      · exact Or.inl ⟨hzQ, hz⟩
      · refine Or.inr ?_
        rintro ⟨x, hxK, rfl⟩
        exact hzQ (Q.map_source (hKS hxK))
  have heq : EqOn e d (e.source ∩ d.source) := by
    intro z hz
    have hzQ : z ∈ Q.target := (hES ▸ hz.1).1
    have hxS : Q.symm z ∈ Q.source := Q.map_target hzQ
    have hxK : Q.symm z ∉ K := by
      intro hx
      exact hz.2 ⟨Q.symm z, hx, Q.right_inv hzQ⟩
    change Q (H (Q.symm z)) = z
    rw [hfix ⟨hxS, hxK⟩]
    exact Q.right_inv hzQ
  obtain ⟨f, hf, hfe, hfd⟩ := e.exists_union_localHomeomorph d heq
  refine ⟨f, hcover ▸ hf, ?_, hfe, hfd⟩
  intro z hz
  have hzcover : z ∈ e.source ∪ d.source := hcover.symm ▸ hz
  rcases hzcover with hze | hzd
  · rw [hfe hze]
    have hzH : Q.symm z ∈ H.source := hze.2.1
    exact himage ⟨H (Q.symm z), H.map_source hzH, rfl⟩
  · rw [hfd hzd]
    exact houtside hzd

end OpenPartialHomeomorph
