import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Winding



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "Circle" => AddCircle (4 * (8 : ℝ))

private instance : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩

theorem exists_cut_fixed_cylinder_lift
    (g : (I × Circle) ≃ₜ (I × Circle))
    (hzero : ∀ z, g (0, z) = (0, z))
    (hone : ∀ z, g (1, z) = (1, z))
    (hcut : ∀ t, g (t, 0) = (t, 0)) :
    ∃ L : C(I × Circle, ℝ),
      (∀ x, (L x : Circle) = (g x).2 - x.2) ∧
      (∀ z, L (0, z) = 0) ∧ (∀ z, L (1, z) = 0) ∧
      (∀ t, L (t, 0) = 0) ∧
      ∀ (t : I) (s : ℝ), s ∈ Icc 0 32 →
        s + L (t, (s : Circle)) ∈ Icc 0 32 := by
  let error : C(I × Circle, Circle) := ⟨fun x => (g x).2 - x.2, by fun_prop⟩
  let z : C(Circle, ℝ) := ContinuousMap.const Circle 0
  have he0 (a : Circle) : error (0, a) = (z a : Circle) := by
    change (g (0, a)).2 - a = 0
    rw [hzero]
    simp
  let cov := AddCircle.isCoveringMap_coe (4 * (8 : ℝ))
  let L := cov.liftHomotopy error z he0
  have hlift (x : I × Circle) : (L x : Circle) = (g x).2 - x.2 :=
    congrFun (cov.liftHomotopy_lifts error z he0) x
  have hL0 (a : Circle) : L (0, a) = 0 := cov.liftHomotopy_zero error z he0 a
  have hLc (t : I) : L (t, 0) = 0 := by
    rw [cov.const_of_comp (g := fun t : I => L (t, 0)) (by fun_prop)
      (fun t u => by rw [hlift, hlift, hcut, hcut]) t 0, hL0]
  have hL1 (a : Circle) : L (1, a) = 0 := by
    rw [cov.const_of_comp (g := fun a : Circle => L (1, a)) (by fun_prop)
      (fun a b => by rw [hlift, hlift, hone, hone]; simp) a 0, hLc]
  have hperiod : ((32 : ℝ) : Circle) = 0 := by
    exact (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨1, by norm_num⟩
  have hnonzero (s : ℝ) (hs : s ∈ Ioo 0 32) : (s : Circle) ≠ 0 := by
    intro hz
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (p := 4 * (8 : ℝ)) (show s ∈ Ico 0 (4 * (8 : ℝ)) by
        constructor <;> linarith [hs.1, hs.2])).mp hz
    linarith [hs.1]
  have havoid (s : ℝ) (hs : s ∈ Ioo 0 32) (t : I) :
      s + L (t, (s : Circle)) ≠ 0 ∧ s + L (t, (s : Circle)) ≠ 32 := by
    have hgc : (g (t, (s : Circle))).2 ≠ 0 := by
      intro h
      have he : g (t, (s : Circle)) = g ((g (t, (s : Circle))).1, 0) := by
        rw [hcut]
        exact Prod.ext rfl h
      exact hnonzero s hs (congrArg Prod.snd (g.injective he))
    have hval : ((s + L (t, (s : Circle)) : ℝ) : Circle) =
        (g (t, (s : Circle))).2 := by
      rw [AddCircle.coe_add, hlift]
      abel
    constructor
    · intro h
      exact hgc (hval.symm.trans (by rw [h]; rfl))
    · intro h
      exact hgc (hval.symm.trans (by rw [h]; exact hperiod))
  refine ⟨L, hlift, hL0, hL1, hLc, ?_⟩
  intro t s hs
  by_cases h0 : s = 0
  · subst s
    simp [hLc]
  by_cases h32 : s = 32
  · subst s
    simp [hperiod, hLc]
  have hs' : s ∈ Ioo 0 32 := ⟨lt_of_le_of_ne hs.1 (Ne.symm h0),
    lt_of_le_of_ne hs.2 h32⟩
  let f : I → ℝ := fun u => s + L (u, (s : Circle))
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = s := by simp [f, hL0]
  constructor
  · by_contra hn
    have hn' : f t < 0 := lt_of_not_ge hn
    obtain ⟨u, _, hu⟩ := intermediate_value_Icc' (show (0 : I) ≤ t from bot_le)
      hf.continuousOn (show (0 : ℝ) ∈ Icc (f t) (f 0) by rw [hf0]; exact ⟨hn'.le, hs.1⟩)
    exact (havoid s hs' u).1 hu
  · by_contra hn
    have hn' : 32 < f t := lt_of_not_ge hn
    obtain ⟨u, _, hu⟩ := intermediate_value_Icc (show (0 : I) ≤ t from bot_le)
      hf.continuousOn (show (32 : ℝ) ∈ Icc (f 0) (f t) by rw [hf0]; exact ⟨hs.2, hn'.le⟩)
    exact (havoid s hs' u).2 hu

private theorem exists_cut_fixed_square_map
    (g : (I × Circle) ≃ₜ (I × Circle))
    (hzero : ∀ z, g (0, z) = (0, z))
    (hone : ∀ z, g (1, z) = (1, z))
    (hcut : ∀ t, g (t, 0) = (t, 0)) :
    ∃ f : C(I × I, I × I),
      (∀ x, ((f x).1, ((32 * ((f x).2 : ℝ) : ℝ) : Circle)) =
        g (x.1, ((32 * (x.2 : ℝ) : ℝ) : Circle))) ∧
      ∀ x, x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1 → f x = x := by
  obtain ⟨L, hL, hL0, hL1, hLc, hbound⟩ :=
    exists_cut_fixed_cylinder_lift g hzero hone hcut
  let a (x : I × I) : ℝ := 32 * (x.2 : ℝ) + L (x.1, ((32 * (x.2 : ℝ) : ℝ) : Circle))
  have ha (x : I × I) : a x ∈ Icc 0 32 :=
    hbound x.1 _ ⟨by linarith [x.2.property.1], by linarith [x.2.property.2]⟩
  let f : C(I × I, I × I) :=
    ⟨fun x => ((g (x.1, ((32 * (x.2 : ℝ) : ℝ) : Circle))).1,
      ⟨a x / 32, by constructor <;> linarith [ (ha x).1, (ha x).2]⟩), by
        dsimp [a]
        fun_prop⟩
  have hperiod : ((32 : ℝ) : Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨1, by norm_num⟩
  refine ⟨f, ?_, ?_⟩
  · intro x
    apply Prod.ext
    · rfl
    · change ((32 * (a x / 32) : ℝ) : Circle) = _
      rw [show 32 * (a x / 32) = a x by ring]
      dsimp [a]
      rw [hL]
      abel
  · rintro ⟨t, s⟩ (ht | ht | hs | hs)
    · change t = 0 at ht
      subst t
      apply Prod.ext
      · exact congrArg (fun y : I × Circle => y.1) (hzero _)
      · apply Subtype.ext
        change (32 * (s : ℝ) + L (0, ((32 * (s : ℝ) : ℝ) : Circle))) / 32 = s
        rw [hL0]
        ring
    · change t = 1 at ht
      subst t
      apply Prod.ext
      · exact congrArg (fun y : I × Circle => y.1) (hone _)
      · apply Subtype.ext
        change (32 * (s : ℝ) + L (1, ((32 * (s : ℝ) : ℝ) : Circle))) / 32 = s
        rw [hL1]
        ring
    · change s = 0 at hs
      subst s
      apply Prod.ext
      · change (g (t, ((32 * (0 : ℝ) : ℝ) : Circle))).1 = t
        simpa using congrArg Prod.fst (hcut t)
      · apply Subtype.ext
        change (32 * (0 : ℝ) + L (t, ((32 * (0 : ℝ) : ℝ) : Circle))) / 32 = 0
        simp [hLc]
    · change s = 1 at hs
      subst s
      apply Prod.ext
      · change (g (t, ((32 * (1 : ℝ) : ℝ) : Circle))).1 = t
        simpa [hperiod] using congrArg Prod.fst (hcut t)
      · apply Subtype.ext
        change (32 * (1 : ℝ) + L (t, ((32 * (1 : ℝ) : ℝ) : Circle))) / 32 = 1
        simp [hperiod, hLc]

theorem exists_cut_fixed_square_homeomorph
    (g : (I × Circle) ≃ₜ (I × Circle))
    (hzero : ∀ z, g (0, z) = (0, z))
    (hone : ∀ z, g (1, z) = (1, z))
    (hcut : ∀ t, g (t, 0) = (t, 0)) :
    ∃ f : (I × I) ≃ₜ (I × I),
      (∀ x, ((f x).1, ((32 * ((f x).2 : ℝ) : ℝ) : Circle)) =
        g (x.1, ((32 * (x.2 : ℝ) : ℝ) : Circle))) ∧
      ∀ x, x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1 → f x = x := by
  obtain ⟨f, hf, hfix⟩ := exists_cut_fixed_square_map g hzero hone hcut
  obtain ⟨fi, hfi, hfixi⟩ := exists_cut_fixed_square_map g.symm
    (fun z => (g.symm_apply_eq.mpr (hzero z).symm))
    (fun z => (g.symm_apply_eq.mpr (hone z).symm))
    (fun t => (g.symm_apply_eq.mpr (hcut t).symm))
  let Q (x : I × I) : I × Circle := (x.1, ((32 * (x.2 : ℝ) : ℝ) : Circle))
  have hunique (a b : C(I × I, I × I))
      (hab : ∀ x, Q (a x) = Q (b x))
      (hbase : a (0, 0) = b (0, 0)) : a = b := by
    have heq : (fun x => 32 * ((a x).2 : ℝ)) = fun x => 32 * ((b x).2 : ℝ) :=
      (AddCircle.isCoveringMap_coe (4 * (8 : ℝ))).eq_of_comp_eq
        (by fun_prop) (by fun_prop)
        (funext fun x => congrArg Prod.snd (hab x)) (0, 0)
        (by rw [hbase])
    apply ContinuousMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun y : I × Circle => y.1) (hab x)
    · apply Subtype.ext
      have := congrFun heq x
      linarith
  have hleft : fi.comp f = ContinuousMap.id (I × I) := by
    apply hunique
    · intro x
      change Q (fi (f x)) = Q x
      dsimp only [Q]
      rw [hfi, hf, g.symm_apply_apply]
    · change fi (f (0, 0)) = (0, 0)
      rw [hfix _ (Or.inl rfl), hfixi _ (Or.inl rfl)]
  have hright : f.comp fi = ContinuousMap.id (I × I) := by
    apply hunique
    · intro x
      change Q (f (fi x)) = Q x
      dsimp only [Q]
      rw [hf, hfi, g.apply_symm_apply]
    · change f (fi (0, 0)) = (0, 0)
      rw [hfixi _ (Or.inl rfl), hfix _ (Or.inl rfl)]
  exact ⟨{ toFun := f
           invFun := fi
           left_inv := fun x => congrFun (congrArg DFunLike.coe hleft) x
           right_inv := fun x => congrFun (congrArg DFunLike.coe hright) x
           continuous_toFun := f.continuous
           continuous_invFun := fi.continuous }, hf, hfix⟩

end PoincareConjecture.M76.Dehn
