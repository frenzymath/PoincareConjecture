import PoincareConjecture.Proofs.M76.Mathlib.StableProductCompletion












set_option autoImplicit false

open Set

namespace IsLocalHomeomorphOn




theorem prodMap {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W] {f : X → Y} {g : Z → W}
    {U : Set X} {V : Set Z} (hf : IsLocalHomeomorphOn f U)
    (hg : IsLocalHomeomorphOn g V) :
    IsLocalHomeomorphOn (Prod.map f g) (U ×ˢ V) := by
  intro z hz
  obtain ⟨e, hze, he⟩ := hf z.1 hz.1
  obtain ⟨d, hzd, hd⟩ := hg z.2 hz.2
  refine ⟨e.prod d, ⟨hze, hzd⟩, ?_⟩
  funext p
  exact Prod.ext (congrFun he p.1) (congrFun hd p.2)

end IsLocalHomeomorphOn

namespace StableCylinder

variable {X Y C : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace C]



def swapLast (X C : Type*) [TopologicalSpace X] [TopologicalSpace C] :
    ((X × C) × ℝ) ≃ₜ ((X × ℝ) × C) where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop



def overBase (X : Type*) [TopologicalSpace X] (L : (C × ℝ) ≃ₜ (C × ℝ)) :
    ((X × C) × ℝ) ≃ₜ ((X × C) × ℝ) :=
  (Homeomorph.prodAssoc X C ℝ).trans
    (((Homeomorph.refl X).prodCongr L).trans (Homeomorph.prodAssoc X C ℝ).symm)



def middleMap (f : X × ℝ → Y × ℝ) (z : (X × C) × ℝ) : (Y × C) × ℝ :=
  (( (f (z.1.1, z.2)).1, z.1.2), (f (z.1.1, z.2)).2)




theorem isLocalHomeomorphOn_middleMap (f : X × ℝ → Y × ℝ)
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1)) :
    IsLocalHomeomorphOn (middleMap (C := C) f) (univ ×ˢ Ioo (-1) 1) := by
  have hprod := hf.prodMap (V := (univ : Set C))
    (Homeomorph.refl C).isLocalHomeomorph.isLocalHomeomorphOn
  have hfirst : IsLocalHomeomorphOn
      (Prod.map f id ∘ swapLast X C) (univ ×ˢ Ioo (-1) 1) :=
    hprod.comp (swapLast X C).isLocalHomeomorph.isLocalHomeomorphOn
      (fun _ hz => ⟨⟨mem_univ _, hz.2⟩, mem_univ _⟩)
  exact (swapLast Y C).symm.isLocalHomeomorph.isLocalHomeomorphOn.comp hfirst
    (fun _ _ => mem_univ _)



def conjugation (L : (C × ℝ) ≃ₜ (C × ℝ)) (f : X × ℝ → Y × ℝ) :
    (X × C) × ℝ → (Y × C) × ℝ :=
  overBase Y L.symm ∘ middleMap f ∘ overBase X L






theorem conjugation_isLocalHomeomorphOn (L : (C × ℝ) ≃ₜ (C × ℝ))
    (hL : MapsTo L (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1))
    (hLi : MapsTo L.symm (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1))
    (f : X × ℝ → Y × ℝ)
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1))
    (hfimage : MapsTo f (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1)) :
    IsLocalHomeomorphOn (conjugation L f) (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo (conjugation L f) (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      ∀ z ∈ univ ×ˢ Ioo (-1) 1,
        ∃ t ∈ Ioo (-1) 1, (conjugation L f z).1.1 = (f (z.1.1, t)).1 := by
  have hpre : MapsTo (overBase X L) (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) :=
    fun _ hz => ⟨mem_univ _, (hL ⟨mem_univ _, hz.2⟩).2⟩
  have hmid : MapsTo (middleMap (C := C) f)
      (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) :=
    fun _ hz => ⟨mem_univ _, (hfimage ⟨mem_univ _, hz.2⟩).2⟩
  have hpost : MapsTo (overBase Y L.symm)
      (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) :=
    fun _ hz => ⟨mem_univ _, (hLi ⟨mem_univ _, hz.2⟩).2⟩
  refine ⟨(overBase Y L.symm).isLocalHomeomorph.isLocalHomeomorphOn.comp
    ((isLocalHomeomorphOn_middleMap f hf).comp
      (overBase X L).isLocalHomeomorph.isLocalHomeomorphOn hpre)
        (fun _ _ => mem_univ _), ?_, ?_⟩
  · exact fun _ hz => hpost (hmid (hpre hz))
  · intro z hz
    exact ⟨(L (z.1.2, z.2)).2, (hL ⟨mem_univ _, hz.2⟩).2, rfl⟩




theorem conjugation_old_product (L : (C × ℝ) ≃ₜ (C × ℝ))
    (hL : MapsTo L (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1))
    (f : X × ℝ → Y × ℝ) (g : X → Y) (U : Set X)
    (hprod : EqOn f (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-1) 1))
    {x : X} (hx : x ∈ U) (c : C) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    conjugation L f ((x, c), t) = ((g x, c), t) := by
  have hv : f (x, (L (c, t)).2) = (g x, (L (c, t)).2) :=
    hprod ⟨hx, (hL ⟨mem_univ _, ht⟩).2⟩
  change (( (f (x, (L (c, t)).2)).1,
    (L.symm ((L (c, t)).1, (f (x, (L (c, t)).2)).2)).1),
      (L.symm ((L (c, t)).1, (f (x, (L (c, t)).2)).2)).2) = _
  rw [hv]
  change ((g x, (L.symm (L (c, t))).1), (L.symm (L (c, t))).2) = _
  rw [L.symm_apply_apply]




theorem conjugation_new_product (L : (C × ℝ) ≃ₜ (C × ℝ))
    (q : ℝ → C) (f : X × ℝ → Y × ℝ) {a delta : ℝ} (hda : delta ≤ a)
    (hrot : ∀ s : ℝ, |s| ≤ a → ∀ t : ℝ, |t| ≤ a → L (q s, t) = (q (-t), s))
    (hinv : ∀ s : ℝ, |s| ≤ a → ∀ t : ℝ, |t| ≤ a → L.symm (q s, t) = (q t, -s))
    (hheight : ∀ x : X, ∀ s : ℝ, |s| ≤ delta → |(f (x, s)).2| ≤ a)
    (x : X) {s t : ℝ} (hs : |s| ≤ delta) (ht : |t| ≤ delta) :
    conjugation L f ((x, q s), t) = (((f (x, s)).1, q (f (x, s)).2), t) := by
  have hLval := hrot s (hs.trans hda) t (ht.trans hda)
  have hLi := hinv (-t) (by simpa only [abs_neg] using ht.trans hda)
    (f (x, s)).2 (hheight x s hs)
  change (( (f (x, (L (q s, t)).2)).1,
    (L.symm ((L (q s, t)).1, (f (x, (L (q s, t)).2)).2)).1),
      (L.symm ((L (q s, t)).1, (f (x, (L (q s, t)).2)).2)).2) = _
  rw [hLval]
  simp only [hLi, neg_neg]

end StableCylinder
