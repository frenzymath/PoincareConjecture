import PoincareConjecture.Proofs.M76.Mathlib.TorusCrossingBandImmersion

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

theorem exists_supported_chart_homeomorph {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    (Q : OpenPartialHomeomorph E X) (H : E ≃ₜ E)
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ Q.source)
    (hfix : EqOn H id Kᶜ) :
    ∃ F : X ≃ₜ X,
      EqOn F (Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)) Q.target ∧
      EqOn F id (Q '' K)ᶜ := by
  have hpres (G : E ≃ₜ E) (hG : EqOn G id Kᶜ) : MapsTo G Q.source Q.source := by
    intro x hx
    by_contra hn
    have hnotK : G x ∉ K := fun h => hn (hKS h)
    have he : G x = x := G.injective (hG hnotK)
    exact hn (he.symm ▸ hx)
  have hinvfix : EqOn H.symm id Kᶜ := by
    intro x hx
    change H.symm x = x
    apply H.injective
    rw [H.apply_symm_apply, show H x = x from hfix hx]
  let e := Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)
  have heS : e.source = Q.target := by
    ext z
    change (z ∈ Q.target ∧ Q.symm z ∈ univ ∧ H (Q.symm z) ∈ Q.source) ↔ z ∈ Q.target
    exact ⟨And.left, fun hz => ⟨hz, mem_univ _, hpres H hfix (Q.map_target hz)⟩⟩
  have heT : e.target = Q.target := by
    ext z
    change ((z ∈ Q.target ∧ Q.symm z ∈ univ) ∧ H.symm (Q.symm z) ∈ Q.source) ↔
      z ∈ Q.target
    exact ⟨fun hz => hz.1.1,
      fun hz => ⟨⟨hz, mem_univ _⟩, hpres H.symm hinvfix (Q.map_target hz)⟩⟩
  have hQK : IsCompact (Q '' K) :=
    hK.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)
  let O := (Q '' K)ᶜ
  let d := OpenPartialHomeomorph.ofSet O hQK.isClosed.isOpen_compl
  have hdS : d.source = O := rfl
  have hcover : e.source ∪ d.source = univ := by
    rw [heS, hdS]
    apply eq_univ_of_forall
    intro z
    by_cases hzQ : z ∈ Q.target
    · exact Or.inl hzQ
    · refine Or.inr ?_
      rintro ⟨x, hx, rfl⟩
      exact hzQ (Q.map_source (hKS hx))
  have heq : EqOn e d (e.source ∩ d.source) := by
    intro z hz
    have hzQ : z ∈ Q.target := heS ▸ hz.1
    have hxK : Q.symm z ∉ K := by
      intro hx
      exact hz.2 ⟨Q.symm z, hx, Q.right_inv hzQ⟩
    change Q (H (Q.symm z)) = z
    rw [hfix hxK]
    exact Q.right_inv hzQ
  obtain ⟨f, hf, hfe, hfd⟩ := e.exists_union_localHomeomorph d heq
  have hfglobal : IsLocalHomeomorph f :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr (hcover ▸ hf)
  have hfout : EqOn f id Q.targetᶜ := by
    intro z hz
    apply hfd
    rintro ⟨x, hx, rfl⟩
    exact hz (Q.map_source (hKS hx))
  have hfin : MapsTo f Q.target Q.target := by
    intro z hz
    have hze : z ∈ e.source := heS.symm ▸ hz
    rw [hfe hze]
    exact heT ▸ e.map_source hze
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      by_cases hx : x ∈ Q.target
      · by_cases hy : y ∈ Q.target
        · have hxe : x ∈ e.source := heS.symm ▸ hx
          have hye : y ∈ e.source := heS.symm ▸ hy
          exact e.injOn hxe hye (by simpa only [hfe hxe, hfe hye] using hxy)
        · have hfy : f y = y := hfout hy
          exact (hy (hfy ▸ hxy ▸ hfin hx)).elim
      · by_cases hy : y ∈ Q.target
        · have hfx : f x = x := hfout hx
          exact (hx (hfx ▸ hxy.symm ▸ hfin hy)).elim
        · simpa only [hfout hx, hfout hy, id_eq] using hxy
    · intro y
      by_cases hy : y ∈ Q.target
      · have hyt : y ∈ e.target := heT.symm ▸ hy
        refine ⟨e.symm y, ?_⟩
        rw [hfe (e.map_target hyt)]
        exact e.right_inv hyt
      · exact ⟨y, hfout hy⟩
  refine ⟨hfglobal.toHomeomorphOfBijective hbij, ?_, ?_⟩
  · intro z hz
    exact hfe (heS.symm ▸ hz)
  · exact hfd

end OpenPartialHomeomorph
