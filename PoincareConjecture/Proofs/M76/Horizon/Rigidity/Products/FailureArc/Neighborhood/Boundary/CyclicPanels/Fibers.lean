import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Strip



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

theorem ordered_panel_fibers
    {X : Type*} (f : Fin 8 → P2 → X)
    (hfi : ∀ i, InjOn (f i) Rect)
    (hseam : ∀ i j : Fin 8, i.val + 1 = j.val → ∀ t ∈ I, f i (1,t) = f j (0,t))
    (hclose : ∀ t ∈ I, f 7 (1,t) = f 0 (0,t))
    (hcontact : ∀ i j : Fin 8, i.val + 1 = j.val →
      (f i '' Rect) ∩ (f j '' Rect) = f i '' ({1} ×ˢ I))
    (hend : (f 0 '' Rect) ∩ (f 7 '' Rect) = f 0 '' ({0} ×ˢ I))
    (hfar : ∀ i j : Fin 8, i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = 7) → Disjoint (f i '' Rect) (f j '' Rect))
    {i j : Fin 8} (hij : i < j) {x y : P2} (hx : x ∈ Rect) (hy : y ∈ Rect)
    (hxy : f i x = f j y) :
    (i.val + 1 = j.val ∧ x.1 = 1 ∧ y.1 = 0 ∧ x.2 = y.2) ∨
      (i = 0 ∧ j = 7 ∧ x.1 = 0 ∧ y.1 = 1 ∧ x.2 = y.2) := by
  have hboth : f i x ∈ (f i '' Rect) ∩ (f j '' Rect) :=
    ⟨⟨x,hx,rfl⟩,⟨y,hy,hxy.symm⟩⟩
  by_cases hn : i.val + 1 = j.val
  · obtain ⟨z,hz,hzx⟩ := (hcontact i j hn).subset hboth
    have hzRect : z ∈ Rect := ⟨by rw [hz.1]; norm_num,hz.2⟩
    have hzx' : z = x := hfi i hzRect hx hzx
    have hx1 : x.1 = 1 := hzx' ▸ hz.1
    have hy0 : (0,x.2) ∈ Rect := ⟨by norm_num,hx.2⟩
    have heq : (0,x.2) = y := hfi j hy0 hy
      ((hseam i j hn x.2 hx.2).symm.trans (by simpa only [← hx1,Prod.mk.eta] using hxy))
    have htime := congrArg (fun z : P2 => z.2) heq
    exact Or.inl ⟨hn,hx1,(congrArg Prod.fst heq).symm,htime⟩
  · have hlt : i.val + 1 < j.val := by have hi : i.val < j.val := hij; omega
    have hends : i = 0 ∧ j = 7 := by
      by_contra h
      exact (Set.disjoint_left.mp (hfar i j hlt h)) hboth.1 hboth.2
    rcases hends with ⟨rfl,rfl⟩
    obtain ⟨z,hz,hzx⟩ := hend.subset hboth
    have hzRect : z ∈ Rect := ⟨by rw [hz.1]; norm_num,hz.2⟩
    have hzx' : z = x := hfi 0 hzRect hx hzx
    have hx0 : x.1 = 0 := hzx' ▸ hz.1
    have hy1 : (1,x.2) ∈ Rect := ⟨by norm_num,hx.2⟩
    have heq : (1,x.2) = y := hfi 7 hy1 hy
      ((hclose x.2 hx.2).trans (by simpa only [← hx0,Prod.mk.eta] using hxy))
    have htime := congrArg (fun z : P2 => z.2) heq
    exact Or.inr ⟨rfl,rfl,hx0,(congrArg Prod.fst heq).symm,htime⟩

theorem cut_strip_fibers
    {X : Type*} (f : Fin 8 → P2 → X) (g : P2 → X)
    (hfi : ∀ i, InjOn (f i) Rect)
    (hseam : ∀ i j : Fin 8, i.val + 1 = j.val → ∀ t ∈ I, f i (1,t) = f j (0,t))
    (hclose : ∀ t ∈ I, f 7 (1,t) = f 0 (0,t))
    (hcontact : ∀ i j : Fin 8, i.val + 1 = j.val →
      (f i '' Rect) ∩ (f j '' Rect) = f i '' ({1} ×ˢ I))
    (hend : (f 0 '' Rect) ∩ (f 7 '' Rect) = f 0 '' ({0} ×ˢ I))
    (hfar : ∀ i j : Fin 8, i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = 7) → Disjoint (f i '' Rect) (f j '' Rect))
    (hvalue : ∀ i p, p ∈ block i → g p = f i (p.1 - i.val,p.2)) :
    ∀ p ∈ Icc (0 : ℝ) 8 ×ˢ I, ∀ q ∈ Icc (0 : ℝ) 8 ×ˢ I,
      g p = g q ↔ p = q ∨ (p.1 = 0 ∧ q.1 = 8 ∧ p.2 = q.2) ∨
        (q.1 = 0 ∧ p.1 = 8 ∧ q.2 = p.2) := by
  have hclosed (t : ℝ) (ht : t ∈ I) : g (0,t) = g (8,t) := by
    rw [hvalue 0 _ (by exact ⟨by norm_num,ht⟩),
      hvalue 7 _ (by exact ⟨by norm_num,ht⟩)]
    norm_num
    exact (hclose t ht).symm
  have hforward (p q : P2) (hp : p ∈ Icc (0 : ℝ) 8 ×ˢ I)
      (hq : q ∈ Icc (0 : ℝ) 8 ×ˢ I) (heq : g p = g q) :
      p = q ∨ (p.1 = 0 ∧ q.1 = 8 ∧ p.2 = q.2) ∨
        (q.1 = 0 ∧ p.1 = 8 ∧ q.2 = p.2) := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp (block_cover.symm ▸ hp)
    obtain ⟨j,hj⟩ := mem_iUnion.mp (block_cover.symm ▸ hq)
    have hpi : (p.1 - i.val,p.2) ∈ Rect := by
      simpa only [shift_value] using shift_mapsTo i hi
    have hqj : (q.1 - j.val,q.2) ∈ Rect := by
      simpa only [shift_value] using shift_mapsTo j hj
    rw [hvalue i p hi,hvalue j q hj] at heq
    have hordered (i j : Fin 8) (hij : i < j)
        (hpi : (p.1 - i.val,p.2) ∈ Rect) (hqj : (q.1 - j.val,q.2) ∈ Rect)
        (heq : f i (p.1 - i.val,p.2) = f j (q.1 - j.val,q.2)) :
        p = q ∨ (p.1 = 0 ∧ q.1 = 8 ∧ p.2 = q.2) := by
      rcases ordered_panel_fibers f hfi hseam hclose hcontact hend hfar hij hpi hqj heq with h | h
      · have hcast : (i.val : ℝ) + 1 = j.val := by exact_mod_cast h.1
        exact Or.inl (Prod.ext (by linarith [h.2.1,h.2.2.1]) h.2.2.2)
      · rcases h with ⟨rfl,rfl,hp0,hq8,hpq⟩
        norm_num at hp0 hq8
        exact Or.inr ⟨hp0,by linarith,hpq⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · rcases hordered i j hij hpi hqj heq with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have h := hfi i hpi hqj heq
      have htime := congrArg (fun z : P2 => z.2) h
      exact Or.inl (Prod.ext (by have hh := congrArg Prod.fst h; dsimp at hh; linarith)
        htime)
    · rcases ordered_panel_fibers f hfi hseam hclose hcontact hend hfar hji hqj hpi heq.symm with h | h
      · have hcast : (j.val : ℝ) + 1 = i.val := by exact_mod_cast h.1
        exact Or.inl (Prod.ext (by linarith [h.2.1,h.2.2.1]) h.2.2.2.symm)
      · rcases h with ⟨rfl,rfl,hq0,hp8,hqp⟩
        norm_num at hq0 hp8
        exact Or.inr (Or.inr ⟨hq0,by linarith,hqp⟩)
  intro p hp q hq
  refine ⟨hforward p q hp hq,?_⟩
  rintro (rfl | ⟨hp0,hq8,ht⟩ | ⟨hq0,hp8,ht⟩)
  · rfl
  · have hpv : p = (0,p.2) := Prod.ext hp0 rfl
    have hqv : q = (8,p.2) := Prod.ext hq8 ht.symm
    rw [hpv,hqv]
    exact hclosed _ hp.2
  · have hqv : q = (0,q.2) := Prod.ext hq0 rfl
    have hpv : p = (8,q.2) := Prod.ext hp8 ht.symm
    rw [hpv,hqv]
    exact (hclosed _ hq.2).symm

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
