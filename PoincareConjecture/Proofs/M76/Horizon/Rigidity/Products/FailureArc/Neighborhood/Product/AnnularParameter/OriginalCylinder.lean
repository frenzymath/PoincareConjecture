import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.SourceCylinder

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.AnnularParameter

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/8 : ℝ)) (1/8)
local notation "Ann" => squareAnnulus (2 : ℝ) (1/8)

theorem exists_original_cylinder
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (f : Fin 8 → P2 → X) (g : P2 → X)
    (hg : PolyhedralPLInCharts e g Ann)
    (hgi : Topology.IsEmbedding (fun x : Ann => g x))
    (hperiod : ∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val+1) → ∀ u : J,
      g (annulusMap 2 (by norm_num) ((s : AddCircle (4*(2 : ℝ))),u)) =
        f i (s-i.val,4*(u : ℝ)+1/2)) :
    ∃ b : V2 × ℝ → X, PolyhedralPLInCharts e b (Rim ×ˢ I) ∧
      InjOn b (Rim ×ˢ I) ∧ b '' (Rim ×ˢ I) = g '' Ann ∧
      (∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val+1) → ∀ t ∈ I,
        b (HamiltonIndexOne.squareCircle ((s : ℝ) : AddCircle (4*(2 : ℝ))),t) = f i (s-i.val,t)) ∧
      ∀ t ∈ I, b '' (Rim ×ˢ {t}) = ⋃ i, f i '' (I ×ˢ {t}) := by
  let : Fact (0 < 4*(2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨C,hC,hCperiod⟩ := exists_source_cylinder
  obtain ⟨v,hv,hvval⟩ := hC.symm
  have hvmap : MapsTo v (Rim ×ˢ I) Ann := by
    intro p hp
    rw [← hvval ⟨p,hp⟩]
    exact (C.symm ⟨p,hp⟩).property
  have hvi : InjOn v (Rim ×ˢ I) := by
    intro p hp q hq h
    exact congrArg Subtype.val (C.symm.injective (Subtype.ext
      ((hvval ⟨p,hp⟩).trans (h.trans (hvval ⟨q,hq⟩).symm))))
  have hvimage : v '' (Rim ×ˢ I) = Ann := by
    apply Subset.antisymm (image_subset_iff.mpr hvmap)
    intro x hx
    refine ⟨C ⟨x,hx⟩,(C ⟨x,hx⟩).property,?_⟩
    exact (hvval (C ⟨x,hx⟩)).symm.trans (congrArg Subtype.val (C.symm_apply_apply ⟨x,hx⟩))
  have hgInj : InjOn g Ann := fun x hx y hy h => congrArg Subtype.val
    (hgi.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  let b := g ∘ v
  have hb : PolyhedralPLInCharts e b (Rim ×ˢ I) := by
    obtain ⟨K,hK,hKs,_⟩ := hv
    exact hKs ▸ hg.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,by assumption⟩ (fun p hp => hvmap (hKs.subset hp))
  have hbperiod (i : Fin 8) (s : ℝ) (hs : s ∈ Icc (i.val : ℝ) (i.val+1))
      (t : ℝ) (ht : t ∈ I) :
      b (HamiltonIndexOne.squareCircle ((s : ℝ) : AddCircle (4*(2 : ℝ))),t) = f i (s-i.val,t) := by
    let u : J := ⟨(t-1/2)/4,by constructor <;> linarith [ht.1,ht.2]⟩
    let q : AddCircle (4*(2 : ℝ)) × J := (s,u)
    let x : Ann := ⟨annulusMap 2 (by norm_num) (q.1,q.2),
      _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) q.1 u⟩
    have htime : 4*(u : ℝ)+1/2=t := by dsimp [u]; ring
    have hx : (C x : V2 × ℝ) = ((HamiltonIndexOne.squareCircle ((s : ℝ) : AddCircle (4*(2 : ℝ))) : V2),t) := by
      simpa only [q,htime] using hCperiod q x rfl
    have hvx : v (HamiltonIndexOne.squareCircle ((s : ℝ) : AddCircle (4*(2 : ℝ))),t) = x := by
      rw [← hx,← hvval,C.symm_apply_apply]
    change g (v _) = _
    rw [hvx]
    exact (hperiod i s hs u).trans (by rw [htime])
  refine ⟨b,hb,hgInj.comp hvi hvmap,?_,hbperiod,?_⟩
  · change (g ∘ v) '' _ = _
    rw [image_comp,hvimage]
  · intro t ht
    ext y
    constructor
    · rintro ⟨⟨z,v⟩,⟨hz,hvt⟩,rfl⟩
      have hv' : v=t := hvt
      subst v
      obtain ⟨θ,hθ⟩ := HamiltonIndexOne.squareCircle.surjective ⟨z,hz⟩
      let s := AddCircle.equivIco (4*(2 : ℝ)) 0 θ
      have hs : (s : ℝ) ∈ Icc (0 : ℝ) 8 := by
        exact ⟨s.property.1,by
          have hupper := s.property.2.le
          norm_num only [show (4 : ℝ) * 2 = 8 by norm_num] at hupper ⊢
          exact hupper⟩
      have hsθ : ((s : ℝ) : AddCircle (4*(2 : ℝ))) = θ := AddCircle.coe_equivIco
      have hblock : ((s : ℝ),t) ∈ Icc (0 : ℝ) 8 ×ˢ I := ⟨hs,ht⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (CyclicPanels.block_cover.symm.subset hblock)
      refine mem_iUnion.mpr ⟨i,((s : ℝ)-i.val,t),⟨⟨by linarith [hi.1.1],by linarith [hi.1.2]⟩,rfl⟩,?_⟩
      rw [← hbperiod i s hi.1 t ht,hsθ,hθ]
    · intro hy
      obtain ⟨i,p,⟨hp,hpt⟩,rfl⟩ := mem_iUnion.mp hy
      have hpt' : p.2=t := hpt
      refine ⟨(HamiltonIndexOne.squareCircle (((p.1+i.val : ℝ)) : AddCircle (4*(2 : ℝ))),t),
        ⟨(HamiltonIndexOne.squareCircle _).property,rfl⟩,?_⟩
      rw [hbperiod i (p.1+i.val) ⟨by linarith [hp.1],by linarith [hp.2]⟩ t ht,add_sub_cancel_right]
      exact congrArg (f i) (Prod.ext rfl hpt'.symm)

end PoincareConjecture.M76.Dehn.Annuli.AnnularParameter
