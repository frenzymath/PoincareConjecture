import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.Attached

set_option autoImplicit false
noncomputable section
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

local notation "I" => Icc (0 : ℝ) 1

theorem attached_collision_of_annular_overlap
    {X A C D : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace C] [CompactSpace C]
    [TopologicalSpace D] [CompactSpace D]
    {N B : Set X} {a : A × I → X}
    (HN : (C × I) ≃ₜ N) (HB : (D × I) ≃ₜ B)
    (ha : Function.Injective a)
    (hinter : N ∩ B = range a)
    {r : A → C} {q : A → D}
    (hNparam : ∀ z t, (HN (r z,t) : X) = a (z,t))
    (hBparam : ∀ z t, (HB (q z,t) : X) = a (z,t))
    (hNside : ∀ x t, (HN (x,t) : X) ∈ range a ↔ ∃ z, r z = x)
    (hBside : ∀ y t, (HB (y,t) : X) ∈ range a ↔ ∃ z, q z = y) :
    ∀ (x : C) (y : D) (s t : I),
      (HN (x,s) : X) = HB (y,t) ↔
        (HN (x,⟨0,by norm_num⟩) : X) = HB (y,⟨0,by norm_num⟩) ∧ s = t := by
  intro x y s t
  constructor
  · intro hxy
    have hnmem : (HN (x,s) : X) ∈ range a := by
      apply hinter.subset
      exact ⟨(HN (x,s)).property, hxy ▸ (HB (y,t)).property⟩
    have hbmem : (HB (y,t) : X) ∈ range a := by
      apply hinter.subset
      exact ⟨hxy ▸ (HN (x,s)).property, (HB (y,t)).property⟩
    obtain ⟨zn,hzn⟩ := (hNside x s).mp hnmem
    obtain ⟨zb,hzb⟩ := (hBside y t).mp hbmem
    have hnval : (HN (x,s) : X) = a (zn,s) := by
      rw [← hzn]
      exact hNparam zn s
    have hbval : (HB (y,t) : X) = a (zb,t) := by
      rw [← hzb]
      exact hBparam zb t
    have hparam : a (zn,s) = a (zb,t) := hnval.symm.trans (hxy.trans hbval)
    have hzt : (zn,s) = (zb,t) := ha hparam
    have hz : zn = zb := congrArg Prod.fst hzt
    have hbottom : (HN (x,⟨0,by norm_num⟩) : X) =
        HB (y,⟨0,by norm_num⟩) := by
      calc
        (HN (x,⟨0,by norm_num⟩) : X) = HN (r zn,⟨0,by norm_num⟩) := by rw [hzn]
        _ = a (zn,⟨0,by norm_num⟩) := hNparam zn _
        _ = a (zb,⟨0,by norm_num⟩) := by rw [hz]
        _ = HB (q zb,⟨0,by norm_num⟩) := (hBparam zb _).symm
        _ = HB (y,⟨0,by norm_num⟩) := by rw [hzb]
    exact ⟨hbottom, congrArg Prod.snd hzt⟩
  · rintro ⟨hbottom,hst⟩
    have hnmem : (HN (x,⟨0,by norm_num⟩) : X) ∈ range a := by
      apply hinter.subset
      exact ⟨(HN (x,⟨0,by norm_num⟩)).property,
        hbottom ▸ (HB (y,⟨0,by norm_num⟩)).property⟩
    have hbmem : (HB (y,⟨0,by norm_num⟩) : X) ∈ range a := by
      apply hinter.subset
      exact ⟨hbottom ▸ (HN (x,⟨0,by norm_num⟩)).property,
        (HB (y,⟨0,by norm_num⟩)).property⟩
    obtain ⟨zn,hzn⟩ := (hNside x ⟨0,by norm_num⟩).mp hnmem
    obtain ⟨zb,hzb⟩ := (hBside y ⟨0,by norm_num⟩).mp hbmem
    have hparam : a (zn,⟨0,by norm_num⟩) = a (zb,⟨0,by norm_num⟩) := by
      calc
        a (zn,⟨0,by norm_num⟩) = HN (r zn,⟨0,by norm_num⟩) := (hNparam zn _).symm
        _ = HN (x,⟨0,by norm_num⟩) := by rw [hzn]
        _ = HB (y,⟨0,by norm_num⟩) := hbottom
        _ = HB (q zb,⟨0,by norm_num⟩) := by rw [hzb]
        _ = a (zb,⟨0,by norm_num⟩) := hBparam zb _
    have hz : zn = zb := congrArg Prod.fst (ha hparam)
    calc
      (HN (x,s) : X) = HN (r zn,s) := by rw [hzn]
      _ = a (zn,s) := hNparam zn s
      _ = a (zb,s) := by rw [hz]
      _ = a (zb,t) := by rw [hst]
      _ = HB (q zb,t) := (hBparam zb t).symm
      _ = HB (y,t) := by rw [hzb]

theorem exists_homeomorph_of_annularly_attached_products
    {X A C D : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace C] [CompactSpace C]
    [TopologicalSpace D] [CompactSpace D]
    {N B : Set X} {a : A × I → X}
    (HN : (C × I) ≃ₜ N) (HB : (D × I) ≃ₜ B)
    (ha : Function.Injective a)
    (hinter : N ∩ B = range a)
    {r : A → C} {q : A → D}
    (hNparam : ∀ z t, (HN (r z,t) : X) = a (z,t))
    (hBparam : ∀ z t, (HB (q z,t) : X) = a (z,t))
    (hNside : ∀ x t, (HN (x,t) : X) ∈ range a ↔ ∃ z, r z = x)
    (hBside : ∀ y t, (HB (y,t) : X) ∈ range a ↔ ∃ z, q z = y) :
    ∃ H : ((range (fun x : C => (HN (x,⟨0,by norm_num⟩) : X)) ∪
        range (fun y : D => (HB (y,⟨0,by norm_num⟩) : X)) : Set X) × I) ≃ₜ
        ((N ∪ B : Set X) : Type),
      (∀ x t, (H (⟨(HN (x,⟨0,by norm_num⟩) : X),
        mem_union_left (range (fun y : D => (HB (y,⟨0,by norm_num⟩) : X)))
          (mem_range_self x)⟩,t) : X) = HN (x,t)) ∧
      ∀ y t, (H (⟨(HB (y,⟨0,by norm_num⟩) : X),
        mem_union_right (range (fun x : C => (HN (x,⟨0,by norm_num⟩) : X)))
          (mem_range_self y)⟩,t) : X) = HB (y,t) := by
  apply exists_homeomorph_of_attached_products HN HB
  exact attached_collision_of_annular_overlap HN HB ha hinter hNparam hBparam hNside hBside

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
