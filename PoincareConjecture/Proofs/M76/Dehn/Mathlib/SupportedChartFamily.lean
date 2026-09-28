import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartInverse

set_option autoImplicit false

open Set Topology

namespace OpenPartialHomeomorph

theorem exists_supported_chart_family {T E X : Type*}
    [TopologicalSpace T] [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    (Q : OpenPartialHomeomorph E X) (H : T → E ≃ₜ E)
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ Q.source)
    (hfix : ∀ t, EqOn (H t) id Kᶜ)
    (hH : Continuous (fun p : T × E => H p.1 p.2))
    (hHinv : Continuous (fun p : T × E => (H p.1).symm p.2)) :
    ∃ G : T → X ≃ₜ X,
      Continuous (fun p : T × X => G p.1 p.2) ∧
      Continuous (fun p : T × X => (G p.1).symm p.2) ∧
      (∀ t, EqOn (G t)
        (Q.symm.trans ((H t).toOpenPartialHomeomorph.trans Q)) Q.target) ∧
      (∀ t, EqOn (G t) id (Q '' K)ᶜ) ∧
      (∀ t, EqOn (G t).symm
        (Q.symm.trans ((H t).symm.toOpenPartialHomeomorph.trans Q)) Q.target) ∧
      (∀ t, EqOn (G t).symm id (Q '' K)ᶜ) := by
  classical
  choose G hGQ hGout using fun t =>
    Q.exists_supported_chart_homeomorph (H t) hK hKS (hfix t)
  have hinverse (t : T) :=
    Q.supported_chart_symm_eqOn (H t) (G t) hKS (hfix t) (hGQ t) (hGout t)
  have hcompact : IsCompact (Q '' K) :=
    hK.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)
  have hjoint (A : T → E ≃ₜ E) (B : T → X ≃ₜ X)
      (hA : Continuous (fun p : T × E => A p.1 p.2))
      (hAfix : ∀ t, EqOn (A t) id Kᶜ)
      (hBQ : ∀ t, EqOn (B t)
        (Q.symm.trans ((A t).toOpenPartialHomeomorph.trans Q)) Q.target)
      (hBout : ∀ t, EqOn (B t) id (Q '' K)ᶜ) :
      Continuous (fun p : T × X => B p.1 p.2) := by
    have hsource (t : T) : MapsTo (A t) Q.source Q.source := by
      intro x hx
      by_contra hn
      have hnotK : A t x ∉ K := fun h => hn (hKS h)
      have he : A t x = x := (A t).injective (hAfix t hnotK)
      exact hn (he.symm ▸ hx)
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hp : p.2 ∈ Q.target
    · have hinner : ContinuousAt (fun z : T × X => A z.1 (Q.symm z.2)) p :=
        hA.continuousAt.comp (continuous_fst.continuousAt.prodMk
          ((Q.continuousAt_symm hp).comp continuous_snd.continuousAt))
      have hcoord : ContinuousAt (fun z : T × X => Q (A z.1 (Q.symm z.2))) p :=
        ContinuousAt.comp (f := fun z : T × X => A z.1 (Q.symm z.2)) (x := p)
          (Q.continuousAt (hsource p.1 (Q.map_target hp))) hinner
      apply hcoord.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt
        (Q.open_target.mem_nhds hp)] with z hz
      exact hBQ z.1 hz
    · have hpout : p.2 ∈ (Q '' K)ᶜ := by
        rintro ⟨x, hx, hxp⟩
        exact hp (hxp ▸ Q.map_source (hKS hx))
      apply continuous_snd.continuousAt.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt
        (hcompact.isClosed.isOpen_compl.mem_nhds hpout)] with z hz
      exact hBout z.1 hz
  have hinvfix (t : T) : EqOn (H t).symm id Kᶜ := by
    intro x hx
    apply (H t).injective
    change H t ((H t).symm x) = H t x
    rw [(H t).apply_symm_apply, hfix t hx]
    rfl
  exact ⟨G, hjoint H G hH hfix hGQ hGout,
    hjoint (fun t => (H t).symm) (fun t => (G t).symm) hHinv hinvfix
      (fun t => (hinverse t).1) (fun t => (hinverse t).2),
    hGQ, hGout, fun t => (hinverse t).1, fun t => (hinverse t).2⟩

end OpenPartialHomeomorph
