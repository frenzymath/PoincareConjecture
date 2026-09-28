import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.FourSideParameter
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.MarkedComplementDisks

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

private theorem exists_prescribed_rectangle_parameter
    {E s₀ s₁ l r : Set P2} {a b c d : P2}
    (hE : IsFinitePLBallPair P2 E (frontier E))
    (e₀ : I ≃ₜ s₀) (e₁ : I ≃ₜ s₁) (d₀ : I ≃ₜ l) (d₁ : I ≃ₜ r)
    (he₀ : e₀.IsFinitePL) (he₁ : e₁.IsFinitePL)
    (hd₀ : d₀.IsFinitePL) (hd₁ : d₁.IsFinitePL)
    (he₀a : (e₀ ⟨0,by norm_num⟩ : P2) = a)
    (he₀b : (e₀ ⟨1,by norm_num⟩ : P2) = b)
    (he₁c : (e₁ ⟨0,by norm_num⟩ : P2) = c)
    (he₁d : (e₁ ⟨1,by norm_num⟩ : P2) = d)
    (hd₀a : (d₀ ⟨0,by norm_num⟩ : P2) = a)
    (hd₀c : (d₀ ⟨1,by norm_num⟩ : P2) = c)
    (hd₁b : (d₁ ⟨0,by norm_num⟩ : P2) = b)
    (hd₁d : (d₁ ⟨1,by norm_num⟩ : P2) = d)
    (hsdis : Disjoint s₀ s₁) (hldis : Disjoint l r)
    (h₀l : s₀ ∩ l = {a}) (h₀r : s₀ ∩ r = {b})
    (h₁l : s₁ ∩ l = {c}) (h₁r : s₁ ∩ r = {d})
    (hfront : frontier E = (s₀ ∪ s₁) ∪ (l ∪ r)) :
    ∃ G : Rect ≃ₜ E, G.IsFinitePL ∧
      (∀ t : I, (G ⟨(t,0),⟨t.property,by norm_num⟩⟩ : P2) = e₀ t) ∧
      (∀ t : I, (G ⟨(t,1),⟨t.property,by norm_num⟩⟩ : P2) = e₁ t) ∧
      (∀ t : I, (G ⟨(0,t),⟨by norm_num,t.property⟩⟩ : P2) = d₀ t) ∧
      (∀ t : I, (G ⟨(1,t),⟨by norm_num,t.property⟩⟩ : P2) = d₁ t) := by
  classical
  let height : P2 → ℝ := fun x =>
    if hx : x ∈ l then (d₀.symm ⟨x,hx⟩ : ℝ)
    else if hx : x ∈ r then (d₁.symm ⟨x,hx⟩ : ℝ)
    else if x ∈ s₁ then 1 else 0
  have hleft (t : I) : height (d₀ t) = (t : ℝ) := by
    simp only [height,dif_pos (d₀ t).property]
    exact congrArg Subtype.val (d₀.symm_apply_apply t)
  have hright (t : I) : height (d₁ t) = (t : ℝ) := by
    have hn : (d₁ t : P2) ∉ l := fun hx =>
      Set.disjoint_left.mp hldis hx (d₁ t).property
    simp only [height,dif_neg hn,dif_pos (d₁ t).property]
    exact congrArg Subtype.val (d₁.symm_apply_apply t)
  have hbottom (t : I) : height (e₀ t) = 0 := by
    by_cases hx : (e₀ t : P2) ∈ l
    · have hv : (e₀ t : P2) = a := h₀l.subset ⟨(e₀ t).property,hx⟩
      rw [hv,← hd₀a]
      exact hleft ⟨0,by norm_num⟩
    by_cases hy : (e₀ t : P2) ∈ r
    · have hv : (e₀ t : P2) = b := h₀r.subset ⟨(e₀ t).property,hy⟩
      rw [hv,← hd₁b]
      exact hright ⟨0,by norm_num⟩
    have hz : (e₀ t : P2) ∉ s₁ := Set.disjoint_left.mp hsdis (e₀ t).property
    simp only [height,dif_neg hx,dif_neg hy,if_neg hz]
  have htop (t : I) : height (e₁ t) = 1 := by
    by_cases hx : (e₁ t : P2) ∈ l
    · have hv : (e₁ t : P2) = c := h₁l.subset ⟨(e₁ t).property,hx⟩
      rw [hv,← hd₀c]
      exact hleft ⟨1,by norm_num⟩
    by_cases hy : (e₁ t : P2) ∈ r
    · have hv : (e₁ t : P2) = d := h₁r.subset ⟨(e₁ t).property,hy⟩
      rw [hv,← hd₁d]
      exact hright ⟨1,by norm_num⟩
    simp only [height,dif_neg hx,dif_neg hy,if_pos (e₁ t).property]
  obtain ⟨B,hB,_,hBb,hBt,hBl,hBr⟩ :=
    Homeomorph.exists_height_preserving_rectangle_boundary zero_lt_one e₀ e₁ d₀ d₁
      he₀ he₁ hd₀ hd₁ height hbottom htop hleft hright hldis
      (he₀a.trans hd₀a.symm) (he₀b.trans hd₁b.symm)
      (he₁c.trans hd₀c.symm) (he₁d.trans hd₁d.symm)
  have hrectfront := frontier_rectangle_eq_four_sides zero_le_one zero_le_one
  let H : frontier Rect ≃ₜ frontier E :=
    (Homeomorph.setCongr hrectfront).trans (B.trans (Homeomorph.setCongr hfront.symm))
  have hH : H.IsFinitePL := hB.setCongr hrectfront.symm hfront.symm
  have hrect : IsFinitePLBallPair P2 Rect (frontier Rect) := by
    have h := (isFinitePLBallPair_Icc zero_lt_one).prod
      (isFinitePLBallPair_Icc zero_lt_one)
    simpa only [frontier_prod_eq,isClosed_Icc.closure_eq,frontier_Icc zero_le_one,
      union_comm] using h
  obtain ⟨G,hG,hkeep,_⟩ := hrect.exists_extension hE H hH
  refine ⟨G,hG,?_,?_,?_,?_⟩
  · intro t
    have hx : ((t : ℝ),0) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inl (Or.inl ⟨t.property,rfl⟩))
    exact (congrArg Subtype.val (hkeep ⟨(t,0),hx⟩)).trans (hBb t)
  · intro t
    have hx : ((t : ℝ),1) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inl (Or.inr ⟨t.property,rfl⟩))
    exact (congrArg Subtype.val (hkeep ⟨(t,1),hx⟩)).trans (hBt t)
  · intro t
    have hx : (0,(t : ℝ)) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inr (Or.inl ⟨rfl,t.property⟩))
    exact (congrArg Subtype.val (hkeep ⟨(0,t),hx⟩)).trans (hBl t)
  · intro t
    have hx : (1,(t : ℝ)) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inr (Or.inr ⟨rfl,t.property⟩))
    exact (congrArg Subtype.val (hkeep ⟨(1,t),hx⟩)).trans (hBr t)

open PolygonalCrossingResolution PLAnnularStrip

theorem exists_prescribed_arm_chart
    {c : P2 → P2} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    {t₀ t₁ v : ℝ} (horder : (t₀ = 0 ∧ t₁ = 1) ∨ (t₀ = 1 ∧ t₁ = 0))
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    ∃ d : I ≃ₜ (c '' arm v), d.IsFinitePL ∧
      ∀ t : I, (d t : P2) = c ((1-t)*t₀+t*t₁,v) := by
  let p : ℝ →ᴬ[ℝ] P2 := (ContinuousAffineMap.lineMap t₀ t₁).prod
    (ContinuousAffineMap.const ℝ ℝ v)
  have hpval (t : ℝ) : p t = ((1-t)*t₀+t*t₁,v) := by
    change (AffineMap.lineMap (k := ℝ) t₀ t₁ t,v) = _
    simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,smul_eq_mul]
    congr 1
    ring
  have hpI : MapsTo p I source := by
    intro t ht
    rw [hpval]
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp only [mul_zero,mul_one,zero_add,add_zero] <;>
      exact ⟨⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩,hv⟩
  have hpi : InjOn p I := by
    intro t ht u hu h
    have hfst := congrArg Prod.fst h
    rw [hpval,hpval] at hfst
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      dsimp at hfst <;> nlinarith
  have hpimage : p '' I = arm v := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨(hpI ht).1,by rw [hpval]; rfl⟩
    · rintro ⟨ht,hv'⟩
      rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · refine ⟨x.1,ht,?_⟩
        rw [hpval]
        simp only [mul_zero,mul_one,zero_add]
        exact Prod.ext rfl hv'.symm
      · refine ⟨1-x.1,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
        rw [hpval]
        apply Prod.ext
        · dsimp; ring
        · exact hv'.symm
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKI,_⟩,_⟩,_⟩ := hI
  have hp : FinitePiecewiseAffineOn p I := ⟨K,hK,hKI,K.affineOnFaces_affine p⟩
  have hcp : FinitePiecewiseAffineOn (c ∘ p) I := hc.comp hp hpI
  have hcpi : InjOn (c ∘ p) I := fun x hx y hy h => hpi hx hy (hci (hpI hx) (hpI hy) h)
  have himage : (c ∘ p) '' I = c '' arm v :=
    (image_image c p I).symm.trans (congrArg (fun s => c '' s) hpimage)
  obtain ⟨d,hd,hdval⟩ := hcp.exists_homeomorph_image hcpi
  refine ⟨d.trans (Homeomorph.setCongr himage),hd.setCongr rfl himage,?_⟩
  intro t
  exact (hdval t).trans (congrArg c (hpval t))

private theorem side_image_of_interval_values
    {g : P2 → P2} {s : Set P2} (d : I ≃ₜ s)
    (v : ℝ → P2) (hval : ∀ t : I, g (v t) = d t) :
    g '' (v '' I) = s := by
  ext x
  constructor
  · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
    rw [hval ⟨t,ht⟩]
    exact (d ⟨t,ht⟩).property
  · intro hx
    let t := d.symm ⟨x,hx⟩
    exact ⟨v t,mem_image_of_mem v t.property,
      (hval t).trans (congrArg Subtype.val (d.apply_symm_apply _))⟩

theorem FourSidedProperComplementDisk.exists_prescribed_arm_map
    {X : Type*} [TopologicalSpace X] {c : P2 → P2} {f : P2 → X}
    {exterior : Set X} {center : Set P2}
    (M : FourSidedProperComplementDisk c f exterior center)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source) :
    ∃ g : P2 → P2, FinitePiecewiseAffineOn g Rect ∧ InjOn g Rect ∧
      g '' Rect = M.carrier ∧ g '' frontier Rect = frontier M.carrier ∧
      g '' (I ×ˢ {(0 : ℝ)}) = M.carrier ∩ frontier spanningOuterSquare ∧
      g '' (I ×ˢ {(1 : ℝ)}) = M.carrier ∩ frontier spanningInnerSquare ∧
      g '' ({(0 : ℝ)} ×ˢ I) = c '' arm (-1) ∧
      g '' ({(1 : ℝ)} ×ˢ I) = c '' arm 1 ∧
      (∀ t ∈ I, g (0,t) = c ((1-t)*M.outerEnd+t*M.innerEnd,-1)) ∧
      (∀ t ∈ I, g (1,t) = c ((1-t)*M.outerEnd+t*M.innerEnd,1)) ∧
      g (0,0) = c (M.outerEnd,-1) ∧ g (1,0) = c (M.outerEnd,1) ∧
      g (0,1) = c (M.innerEnd,-1) ∧ g (1,1) = c (M.innerEnd,1) := by
  have hab : c (M.outerEnd,-1) ≠ c (M.outerEnd,1) := fun h =>
    Set.disjoint_left.mp M.opposite_arms
      (M.negative_interval.1 (show c (M.outerEnd,-1) ∈
        ({c (M.outerEnd,-1),c (M.innerEnd,-1)} : Set P2) by simp))
      (h.symm ▸ M.positive_interval.1 (show c (M.outerEnd,1) ∈
        ({c (M.outerEnd,1),c (M.innerEnd,1)} : Set P2) by simp))
  have hcd : c (M.innerEnd,-1) ≠ c (M.innerEnd,1) := fun h =>
    Set.disjoint_left.mp M.opposite_arms
      (M.negative_interval.1 (show c (M.innerEnd,-1) ∈
        ({c (M.outerEnd,-1),c (M.innerEnd,-1)} : Set P2) by simp))
      (h.symm ▸ M.positive_interval.1 (show c (M.innerEnd,1) ∈
        ({c (M.outerEnd,1),c (M.innerEnd,1)} : Set P2) by simp))
  obtain ⟨e₀,he₀,he₀a,he₀b⟩ := M.outer_interval.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨e₁,he₁,he₁c,he₁d⟩ := M.inner_interval.exists_unitInterval_chart_with_endpoints hcd
  obtain ⟨d₀,hd₀,hd₀val⟩ := exists_prescribed_arm_chart hc hci M.endpoint_order
    (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
  obtain ⟨d₁,hd₁,hd₁val⟩ := exists_prescribed_arm_chart hc hci M.endpoint_order
    (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
  have hd₀a : (d₀ ⟨0,by norm_num⟩ : P2) = c (M.outerEnd,-1) := by
    simpa using hd₀val ⟨0,by norm_num⟩
  have hd₀c : (d₀ ⟨1,by norm_num⟩ : P2) = c (M.innerEnd,-1) := by
    simpa using hd₀val ⟨1,by norm_num⟩
  have hd₁b : (d₁ ⟨0,by norm_num⟩ : P2) = c (M.outerEnd,1) := by
    simpa using hd₁val ⟨0,by norm_num⟩
  have hd₁d : (d₁ ⟨1,by norm_num⟩ : P2) = c (M.innerEnd,1) := by
    simpa using hd₁val ⟨1,by norm_num⟩
  obtain ⟨G,hG,hGb,hGt,hGl,hGr⟩ := exists_prescribed_rectangle_parameter M.ball
    e₀ e₁ d₀ d₁ he₀ he₁ hd₀ hd₁ he₀a he₀b he₁c he₁d hd₀a hd₀c hd₁b hd₁d
    M.opposite_rims M.opposite_arms
    (M.outer_contacts (-1) (Or.inl rfl)) (M.outer_contacts 1 (Or.inr rfl))
    (M.inner_contacts (-1) (Or.inl rfl)) (M.inner_contacts 1 (Or.inr rfl)) M.frontier_eq
  obtain ⟨g,hg,hval⟩ := hG
  have hgb (t : I) : g (t,0) = e₀ t :=
    (hval ⟨(t,0),⟨t.property,by norm_num⟩⟩).symm.trans (hGb t)
  have hgt (t : I) : g (t,1) = e₁ t :=
    (hval ⟨(t,1),⟨t.property,by norm_num⟩⟩).symm.trans (hGt t)
  have hgl (t : I) : g (0,t) = d₀ t :=
    (hval ⟨(0,t),⟨by norm_num,t.property⟩⟩).symm.trans (hGl t)
  have hgr (t : I) : g (1,t) = d₁ t :=
    (hval ⟨(1,t),⟨by norm_num,t.property⟩⟩).symm.trans (hGr t)
  have hhorizontal (v : ℝ) : (fun t : ℝ => (t,v)) '' I = I ×ˢ {v} :=
    (prod_singleton (s := I) (b := v)).symm
  have hvertical (v : ℝ) : (fun t : ℝ => (v,t)) '' I = {v} ×ˢ I := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ⟨rfl,ht⟩
    · rintro ⟨hx,hy⟩; exact ⟨x.2,hy,Prod.ext hx.symm rfl⟩
  have hb := side_image_of_interval_values e₀ (fun t => (t,0)) hgb
  have ht := side_image_of_interval_values e₁ (fun t => (t,1)) hgt
  have hl := side_image_of_interval_values d₀ (fun t => (0,t)) hgl
  have hr := side_image_of_interval_values d₁ (fun t => (1,t)) hgr
  rw [hhorizontal] at hb ht
  rw [hvertical] at hl hr
  refine ⟨g,hg,?_,?_,?_,hb,ht,hl,hr,?_,?_,?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hval ⟨x,hx⟩).trans (hxy.trans (hval ⟨y,hy⟩).symm))))
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [← hval ⟨y,hy⟩]
      exact (G ⟨y,hy⟩).property
    · intro hx
      let y := G.symm ⟨x,hx⟩
      exact ⟨y,y.property,(hval y).symm.trans (congrArg Subtype.val (G.apply_symm_apply _))⟩
  · rw [frontier_rectangle_eq_four_sides zero_le_one zero_le_one,
      image_union,image_union,image_union,hb,ht,hl,hr,← M.frontier_eq]
  · intro t ht
    exact (hgl ⟨t,ht⟩).trans (hd₀val ⟨t,ht⟩)
  · intro t ht
    exact (hgr ⟨t,ht⟩).trans (hd₁val ⟨t,ht⟩)
  · exact (hgb ⟨0,by norm_num⟩).trans he₀a
  · exact (hgb ⟨1,by norm_num⟩).trans he₀b
  · exact (hgt ⟨0,by norm_num⟩).trans he₁c
  · exact (hgt ⟨1,by norm_num⟩).trans he₁d

end PoincareConjecture.M76.Dehn.Annuli
