import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapSignedCore
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem selected_endpoint_cut_meets_moved_exterior
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {N : Set E} {R U : Set X}
    (hUc : IsConnected U) (hUR : U ⊆ R) (hN : IsCompact N)
    (c : E × ℝ → X) (hc : ContinuousOn c (N ×ˢ Icc (-1 : ℝ) 1))
    (hi : Topology.IsEmbedding (fun z : (N ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstripR : MapsTo c (N ×ˢ Icc (-δ) δ) R)
    (hin : MapsTo c (N ×ˢ Icc (-δ) 0) U)
    (hinint : MapsTo c (N ×ˢ Ico (-δ) 0) (interior U))
    (hout : Disjoint (c '' (N ×ˢ Ioc 0 δ)) U)
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-δ/12) (δ/12))))
    (hp : ∃ p ∈ U, p ∉ interior U ∧ p ∉ c '' (N ×ˢ Icc (-δ) δ))
    (F : X ≃ₜ X) (hfix : EqOn F id (c '' (N ×ˢ Icc (-δ/2) (δ/2)))ᶜ)
    (hslide : ∀ z ∈ N ×ˢ Icc (-δ/2) (δ/2),
      F (c z) = c (z.1,if z.2 ≤ 0 then (3*z.2+δ/2)/2 else (z.2+δ/2)/2)) :
    let Q := R \ interior U
    let Q' := R \ (c '' (N ×ˢ Ioo (-δ/12) (δ/12)))
    F '' Q ⊆ Q' ∧ ∀ x ∈ Q', ∃ y ∈ Q, F y ∈ connectedComponentIn Q' x := by
  let O := c '' (N ×ˢ Ioo (-δ/12) (δ/12))
  let C := c '' (N ×ˢ Icc (-δ/2) (δ/2))
  have hfull : N ×ˢ Icc (-δ) δ ⊆ N ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hz => ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hhalf : N ×ˢ Icc (-δ/2) (δ/2) ⊆ N ×ˢ Icc (-δ) δ :=
    fun _ hz => ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hCR : C ⊆ R := by rintro _ ⟨z,hz,rfl⟩; exact hstripR (hhalf hz)
  have hFmap : MapsTo F R R := by
    intro x hx
    by_contra hn
    have hFF : F (F x) = F x := hfix (fun h => hn (hCR h))
    exact hn ((F.injective hFF).symm ▸ hx)
  have hinj : InjOn c (N ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  have hOsub : O ⊆ c '' (N ×ˢ Icc (-δ) δ) :=
    image_mono (fun _ hz => ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩)
  have hcore : IsConnected (U \ O) := by
    dsimp only [O]
    rw [neg_div]
    apply isConnected_selected_endpoint_inner_remainder hUc hN c hc hi
      (by positivity : 0 < δ/12) (by linarith : δ/12 ≤ 1)
    · intro z hz
      exact hin ⟨hz.1,by linarith [hz.2.1],hz.2.2⟩
    · apply hout.mono_left
      apply image_mono
      intro z hz
      exact ⟨hz.1,hz.2.1,by linarith [hz.2.2]⟩
    · simpa only [neg_div] using hopen
  refine ⟨?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    refine ⟨hFmap hy.1,?_⟩
    rintro ⟨z,hz,hzy⟩
    let t := (2*z.2-δ/2)/3
    have ht : t ∈ Icc (-δ/2) (δ/2) := by
      dsimp [t]
      constructor <;> linarith [hz.2.1,hz.2.2]
    have htneg : t < 0 := by dsimp [t]; linarith [hz.2.2]
    have heq : F (c (z.1,t)) = F y := by
      rw [hslide (z.1,t) ⟨hz.1,ht⟩,if_pos htneg.le]
      have htval : (3*t+δ/2)/2 = z.2 := by dsimp [t]; ring
      simpa only [htval] using hzy
    have hcy : c (z.1,t) = y := F.injective heq
    apply hy.2
    rw [←hcy]
    exact hinint ⟨hz.1,by linarith [ht.1],htneg⟩
  · intro x hx
    by_cases hxU : x ∈ U
    · obtain ⟨p,hpU,hpi,hpout⟩ := hp
      have hpO : p ∉ O := fun h => hpout (hOsub h)
      have hpfix : F p = p := hfix (fun h => hpout (image_mono hhalf h))
      refine ⟨p,⟨hUR hpU,hpi⟩,?_⟩
      rw [hpfix]
      exact hcore.isPreconnected.subset_connectedComponentIn ⟨hxU,hx.2⟩
        (show U \ O ⊆ R \ O from fun _ h => ⟨hUR h.1,h.2⟩) ⟨hpU,hpO⟩
    · by_cases hxC : x ∈ C
      · obtain ⟨z,hz,hzx⟩ := hxC
        have htpos : 0 < z.2 := by
          by_contra h
          apply hxU
          rw [←hzx]
          exact hin ⟨hz.1,by linarith [hz.2.1],le_of_not_gt h⟩
        have hta : δ/12 ≤ z.2 := by
          by_contra h
          exact hx.2 ⟨z,⟨hz.1,by linarith,lt_of_not_ge h⟩,hzx⟩
        let y := c (z.1,δ/2)
        have hyR : y ∈ R := hstripR ⟨hz.1,by linarith,by linarith⟩
        have hyout : y ∉ U := fun hy => disjoint_left.mp hout
          ⟨(z.1,δ/2),⟨hz.1,by linarith,by linarith⟩,rfl⟩ hy
        have hyfix : F y = y := by
          rw [hslide (z.1,δ/2) ⟨hz.1,by constructor <;> linarith⟩,
            if_neg (by linarith : ¬δ/2 ≤ 0)]
          congr 1
          apply Prod.ext
          · rfl
          · ring
        let A := ({z.1} : Set E) ×ˢ Icc z.2 (δ/2)
        have hAfull : A ⊆ N ×ˢ Icc (-1 : ℝ) 1 := by
          intro w hw
          have hw1 : w.1 = z.1 := hw.1
          exact ⟨hw1.symm ▸ hz.1,by linarith [hw.2.1,hz.2.1],by linarith [hw.2.2]⟩
        have hAconn : IsPreconnected (c '' A) :=
          (isPreconnected_singleton.prod isPreconnected_Icc).image c (hc.mono hAfull)
        have hAQ : c '' A ⊆ R \ O := by
          rintro _ ⟨w,hw,rfl⟩
          have hw1 : w.1 = z.1 := hw.1
          refine ⟨hstripR ⟨hw1.symm ▸ hz.1,by linarith [hw.2.1,hz.2.1],by linarith [hw.2.2]⟩,?_⟩
          rintro ⟨v,hv,hvw⟩
          have hveq := congrArg Prod.snd (hinj
            (hfull ⟨hv.1,by linarith [hv.2.1],by linarith [hv.2.2]⟩) (hAfull hw) hvw)
          linarith [hv.2.2,hw.2.1]
        refine ⟨y,⟨hyR,fun h => hyout (interior_subset h)⟩,?_⟩
        rw [hyfix]
        apply hAconn.subset_connectedComponentIn
          (show x ∈ c '' A from ⟨z,⟨rfl,le_rfl,hz.2.2⟩,hzx⟩) hAQ
        exact ⟨(z.1,δ/2),⟨rfl,hz.2.2,le_rfl⟩,rfl⟩
      · exact ⟨x,⟨hx.1,fun h => hxU (interior_subset h)⟩,
          (hfix hxC).symm ▸ mem_connectedComponentIn hx⟩

end PoincareConjecture.M76
