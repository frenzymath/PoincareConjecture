import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.FourSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.CanonicalFourSides
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRectangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.TruncatedStarRectangleFilling
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval







set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

private theorem horizontal_side_iff
    {E : Set P2} (G : Rect ≃ₜ E) {s : Set P2} (d : I ≃ₜ s)
    {v : ℝ} (hv : v ∈ I)
    (hkeep : ∀ t : I, (G ⟨(t,v),⟨t.property,hv⟩⟩ : P2) = d t)
    (x : Rect) : (G x : P2) ∈ s ↔ (x : P2).2 = v := by
  constructor
  · intro hx
    let t := d.symm ⟨G x,hx⟩
    have heq : G ⟨(t,v),⟨t.property,hv⟩⟩ = G x :=
      Subtype.ext ((hkeep t).trans (congrArg Subtype.val (d.apply_symm_apply _)))
    exact (congrArg (fun z : Rect => (z : P2).2) (G.injective heq)).symm
  · intro hx
    have heq : x = ⟨((x : P2).1,v),⟨x.property.1,hv⟩⟩ :=
      Subtype.ext (Prod.ext rfl hx)
    rw [heq,hkeep ⟨(x : P2).1,x.property.1⟩]
    exact (d ⟨(x : P2).1,x.property.1⟩).property

private theorem vertical_side_iff
    {E : Set P2} (G : Rect ≃ₜ E) {s : Set P2} (d : I ≃ₜ s)
    {v : ℝ} (hv : v ∈ I)
    (hkeep : ∀ t : I, (G ⟨(v,t),⟨hv,t.property⟩⟩ : P2) = d t)
    (x : Rect) : (G x : P2) ∈ s ↔ (x : P2).1 = v := by
  constructor
  · intro hx
    let t := d.symm ⟨G x,hx⟩
    have heq : G ⟨(v,t),⟨hv,t.property⟩⟩ = G x :=
      Subtype.ext ((hkeep t).trans (congrArg Subtype.val (d.apply_symm_apply _)))
    exact (congrArg (fun z : Rect => (z : P2).1) (G.injective heq)).symm
  · intro hx
    have heq : x = ⟨(v,(x : P2).2),⟨hv,x.property.2⟩⟩ :=
      Subtype.ext (Prod.ext hx rfl)
    rw [heq,hkeep ⟨(x : P2).2,x.property.2⟩]
    exact (d ⟨(x : P2).2,x.property.2⟩).property

theorem exists_four_side_disk_parameter
    {E s₀ s₁ l r : Set P2} {a b c d : P2}
    (hE : IsFinitePLBallPair P2 E (frontier E))
    (hs₀ : IsFinitePLBallPair ℝ s₀ {a,b})
    (hs₁ : IsFinitePLBallPair ℝ s₁ {c,d})
    (hl : IsFinitePLBallPair ℝ l {a,c})
    (hr : IsFinitePLBallPair ℝ r {b,d})
    (hsdis : Disjoint s₀ s₁) (hldis : Disjoint l r)
    (h₀l : s₀ ∩ l = {a}) (h₀r : s₀ ∩ r = {b})
    (h₁l : s₁ ∩ l = {c}) (h₁r : s₁ ∩ r = {d})
    (hfront : frontier E = (s₀ ∪ s₁) ∪ (l ∪ r)) :
    ∃ G : Rect ≃ₜ E, G.IsFinitePL ∧
      (∀ x : Rect, (G x : P2) ∈ s₀ ↔ (x : P2).2 = 0) ∧
      (∀ x : Rect, (G x : P2) ∈ s₁ ↔ (x : P2).2 = 1) ∧
      (∀ x : Rect, (G x : P2) ∈ l ↔ (x : P2).1 = 0) ∧
      (∀ x : Rect, (G x : P2) ∈ r ↔ (x : P2).1 = 1) ∧
      (G ⟨(0,0),by norm_num⟩ : P2) = a ∧
      (G ⟨(1,0),by norm_num⟩ : P2) = b ∧
      (G ⟨(0,1),by norm_num⟩ : P2) = c ∧
      (G ⟨(1,1),by norm_num⟩ : P2) = d := by
  classical
  have hab : a ≠ b := fun h => Set.disjoint_left.mp hldis
    (hl.1 (show a ∈ ({a,c} : Set P2) by simp))
    (h.symm ▸ hr.1 (show b ∈ ({b,d} : Set P2) by simp))
  have hcd : c ≠ d := fun h => Set.disjoint_left.mp hldis
    (hl.1 (show c ∈ ({a,c} : Set P2) by simp))
    (h.symm ▸ hr.1 (show d ∈ ({b,d} : Set P2) by simp))
  have hac : a ≠ c := fun h => Set.disjoint_left.mp hsdis
    (hs₀.1 (show a ∈ ({a,b} : Set P2) by simp))
    (h.symm ▸ hs₁.1 (show c ∈ ({c,d} : Set P2) by simp))
  have hbd : b ≠ d := fun h => Set.disjoint_left.mp hsdis
    (hs₀.1 (show b ∈ ({a,b} : Set P2) by simp))
    (h.symm ▸ hs₁.1 (show d ∈ ({c,d} : Set P2) by simp))
  obtain ⟨e₀,he₀,he₀a,he₀b⟩ := hs₀.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨e₁,he₁,he₁c,he₁d⟩ := hs₁.exists_unitInterval_chart_with_endpoints hcd
  obtain ⟨d₀,hd₀,hd₀a,hd₀c⟩ := hl.exists_unitInterval_chart_with_endpoints hac
  obtain ⟨d₁,hd₁,hd₁b,hd₁d⟩ := hr.exists_unitInterval_chart_with_endpoints hbd
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
  have hGb (t : I) : (G ⟨(t,0),⟨t.property,by norm_num⟩⟩ : P2) = e₀ t := by
    have hx : ((t : ℝ),0) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inl (Or.inl ⟨t.property,rfl⟩))
    exact (congrArg Subtype.val (hkeep ⟨(t,0),hx⟩)).trans (hBb t)
  have hGt (t : I) : (G ⟨(t,1),⟨t.property,by norm_num⟩⟩ : P2) = e₁ t := by
    have hx : ((t : ℝ),1) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inl (Or.inr ⟨t.property,rfl⟩))
    exact (congrArg Subtype.val (hkeep ⟨(t,1),hx⟩)).trans (hBt t)
  have hGl (t : I) : (G ⟨(0,t),⟨by norm_num,t.property⟩⟩ : P2) = d₀ t := by
    have hx : (0,(t : ℝ)) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inr (Or.inl ⟨rfl,t.property⟩))
    exact (congrArg Subtype.val (hkeep ⟨(0,t),hx⟩)).trans (hBl t)
  have hGr (t : I) : (G ⟨(1,t),⟨by norm_num,t.property⟩⟩ : P2) = d₁ t := by
    have hx : (1,(t : ℝ)) ∈ frontier Rect :=
      hrectfront.symm.subset (Or.inr (Or.inr ⟨rfl,t.property⟩))
    exact (congrArg Subtype.val (hkeep ⟨(1,t),hx⟩)).trans (hBr t)
  exact ⟨G,hG,horizontal_side_iff G e₀ (by norm_num) hGb,
    horizontal_side_iff G e₁ (by norm_num) hGt,
    vertical_side_iff G d₀ (by norm_num) hGl,
    vertical_side_iff G d₁ (by norm_num) hGr,
    (hGb ⟨0,by norm_num⟩).trans he₀a,(hGb ⟨1,by norm_num⟩).trans he₀b,
    (hGt ⟨0,by norm_num⟩).trans he₁c,(hGt ⟨1,by norm_num⟩).trans he₁d⟩

private theorem side_image_of_parameter
    {E A B : Set P2} (G : Rect ≃ₜ E) {g : P2 → P2}
    (hval : ∀ x : Rect, (G x : P2) = g x)
    (hA : A ⊆ Rect) (hB : B ⊆ E)
    (hmem : ∀ x : Rect, (G x : P2) ∈ B ↔ (x : P2) ∈ A) : g '' A = B := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [← hval ⟨x,hA hx⟩]
    exact (hmem ⟨x,hA hx⟩).mpr hx
  · intro hy
    let x := G.symm ⟨y,hB hy⟩
    have hxy : (G x : P2) = y := congrArg Subtype.val (G.apply_symm_apply _)
    exact ⟨x,(hmem x).mp (hxy.symm ▸ hy),(hval x).symm.trans hxy⟩

theorem exists_four_side_disk_map
    {E s₀ s₁ l r : Set P2} {a b c d : P2}
    (hE : IsFinitePLBallPair P2 E (frontier E))
    (hs₀ : IsFinitePLBallPair ℝ s₀ {a,b})
    (hs₁ : IsFinitePLBallPair ℝ s₁ {c,d})
    (hl : IsFinitePLBallPair ℝ l {a,c})
    (hr : IsFinitePLBallPair ℝ r {b,d})
    (hsdis : Disjoint s₀ s₁) (hldis : Disjoint l r)
    (h₀l : s₀ ∩ l = {a}) (h₀r : s₀ ∩ r = {b})
    (h₁l : s₁ ∩ l = {c}) (h₁r : s₁ ∩ r = {d})
    (hfront : frontier E = (s₀ ∪ s₁) ∪ (l ∪ r)) :
    ∃ g : P2 → P2, FinitePiecewiseAffineOn g Rect ∧ InjOn g Rect ∧
      g '' Rect = E ∧ g '' frontier Rect = frontier E ∧
      g '' (I ×ˢ {(0 : ℝ)}) = s₀ ∧ g '' (I ×ˢ {(1 : ℝ)}) = s₁ ∧
      g '' ({(0 : ℝ)} ×ˢ I) = l ∧ g '' ({(1 : ℝ)} ×ˢ I) = r ∧
      g (0,0) = a ∧ g (1,0) = b ∧ g (0,1) = c ∧ g (1,1) = d := by
  obtain ⟨G,hG,hG₀,hG₁,hGl,hGr,hGa,hGb,hGc,hGd⟩ :=
    exists_four_side_disk_parameter hE hs₀ hs₁ hl hr hsdis hldis
      h₀l h₀r h₁l h₁r hfront
  obtain ⟨g,hg,hval⟩ := hG
  have hE₀ : s₀ ⊆ E := fun _ hx => hE.1 (hfront.symm.subset (Or.inl (Or.inl hx)))
  have hE₁ : s₁ ⊆ E := fun _ hx => hE.1 (hfront.symm.subset (Or.inl (Or.inr hx)))
  have hEl : l ⊆ E := fun _ hx => hE.1 (hfront.symm.subset (Or.inr (Or.inl hx)))
  have hEr : r ⊆ E := fun _ hx => hE.1 (hfront.symm.subset (Or.inr (Or.inr hx)))
  have h₀ : g '' (I ×ˢ {(0 : ℝ)}) = s₀ := side_image_of_parameter G hval
    (by rintro x ⟨hx,hy⟩; exact ⟨hx,hy ▸ (by norm_num : (0 : ℝ) ∈ I)⟩) hE₀
    (fun x => by simpa only [mem_prod,mem_singleton_iff,x.property.1,true_and] using hG₀ x)
  have h₁ : g '' (I ×ˢ {(1 : ℝ)}) = s₁ := side_image_of_parameter G hval
    (by rintro x ⟨hx,hy⟩; exact ⟨hx,hy ▸ (by norm_num : (1 : ℝ) ∈ I)⟩) hE₁
    (fun x => by simpa only [mem_prod,mem_singleton_iff,x.property.1,true_and] using hG₁ x)
  have hl' : g '' ({(0 : ℝ)} ×ˢ I) = l := side_image_of_parameter G hval
    (by rintro x ⟨hx,hy⟩; exact ⟨hx ▸ (by norm_num : (0 : ℝ) ∈ I),hy⟩) hEl
    (fun x => by simpa only [mem_prod,mem_singleton_iff,x.property.2,and_true] using hGl x)
  have hr' : g '' ({(1 : ℝ)} ×ˢ I) = r := side_image_of_parameter G hval
    (by rintro x ⟨hx,hy⟩; exact ⟨hx ▸ (by norm_num : (1 : ℝ) ∈ I),hy⟩) hEr
    (fun x => by simpa only [mem_prod,mem_singleton_iff,x.property.2,and_true] using hGr x)
  refine ⟨g,hg,?_,?_,?_,h₀,h₁,hl',hr',?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hval ⟨x,hx⟩).trans (hxy.trans (hval ⟨y,hy⟩).symm))))
  · exact side_image_of_parameter G hval Subset.rfl Subset.rfl
      (fun x => iff_of_true (G x).property x.property)
  · rw [frontier_rectangle_eq_four_sides zero_le_one zero_le_one,
      image_union,image_union,image_union,h₀,h₁,hl',hr',← hfront]
  · exact (hval ⟨(0,0),by norm_num⟩).symm.trans hGa
  · exact (hval ⟨(1,0),by norm_num⟩).symm.trans hGb
  · exact (hval ⟨(0,1),by norm_num⟩).symm.trans hGc
  · exact (hval ⟨(1,1),by norm_num⟩).symm.trans hGd

open PolygonalCrossingResolution PLAnnularStrip

theorem exists_planar_annulus_four_side_map
    (c : P2 → P2) (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hin : MapsTo c source (squareAnnulus 8 1))
    (hproper : ∀ p ∈ source, c p ∈ frontier (squareAnnulus 8 1) ↔ p.1 = 0 ∨ p.1 = 1)
    (houter : (c '' arm 0 ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (c '' arm 0 ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ (E : Set P2) (t₀ t₁ : ℝ) (g : P2 → P2),
      IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ c '' source = squareAnnulus 8 1 ∧
      E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) ∧ E ⊆ squareAnnulus 8 1 ∧
      ((t₀ = 0 ∧ t₁ = 1) ∨ (t₀ = 1 ∧ t₁ = 0)) ∧
      (∀ p ∈ source, c p ∈ frontier spanningOuterSquare ↔ p.1 = t₀) ∧
      (∀ p ∈ source, c p ∈ frontier spanningInnerSquare ↔ p.1 = t₁) ∧
      FinitePiecewiseAffineOn g Rect ∧ InjOn g Rect ∧
      g '' Rect = E ∧ g '' frontier Rect = frontier E ∧
      g '' (I ×ˢ {(0 : ℝ)}) = E ∩ frontier spanningOuterSquare ∧
      g '' (I ×ˢ {(1 : ℝ)}) = E ∩ frontier spanningInnerSquare ∧
      g '' ({(0 : ℝ)} ×ˢ I) = c '' arm (-1) ∧
      g '' ({(1 : ℝ)} ×ˢ I) = c '' arm 1 ∧
      g (0,0) = c (t₀,-1) ∧ g (1,0) = c (t₀,1) ∧
      g (0,1) = c (t₁,-1) ∧ g (1,1) = c (t₁,1) := by
  obtain ⟨E,t₀,t₁,hE,hcover,hcontact,hEA,horder,ht₀,ht₁,hfront,
      hs₀,hs₁,hl,hr,hsdis,hldis,h₀,h₁⟩ :=
    exists_planar_annulus_four_sided_complement c hc hci hin hproper houter hinner
  obtain ⟨g,hg⟩ := exists_four_side_disk_map hE hs₀ hs₁ hl hr hsdis hldis
    (h₀ (-1) (Or.inl rfl)) (h₀ 1 (Or.inr rfl))
    (h₁ (-1) (Or.inl rfl)) (h₁ 1 (Or.inr rfl)) hfront
  exact ⟨E,t₀,t₁,g,hE,hcover,hcontact,hEA,horder,ht₀,ht₁,hg⟩

end PoincareConjecture.M76.Dehn.Annuli
