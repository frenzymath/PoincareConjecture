import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Collar








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

namespace PoincareConjecture



theorem exists_projectiveHeightGraph_collar
    {M : Type*} [TopologicalSpace M] (f : RoundCylinderSpace → M) {s : ℝ}
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-s) s))
    (hfiber : ∀ z ∈ univ ×ˢ Ioo (-s) s, ∀ w ∈ univ ×ˢ Ioo (-s) s,
      f z = f w ↔ w = z ∨ w = (-z.1, z.2))
    (u : UnitTwoSphere → ℝ) (hu : Continuous u)
    (heven : ∀ q, u (-q) = u q) (hbound : ∀ q, |u q| < s) :
    IsCompact (range (fun q : UnitTwoSphere => f (q, u q))) ∧
      IsConnected (range (fun q : UnitTwoSphere => f (q, u q))) ∧
      ∃ (δ : ℝ) (hδ : 0 < δ) (W : Set M), IsOpen W ∧
        W ⊆ f '' (univ ×ˢ Ioo (-s) s) ∧
        ∃ e : (RealProjectiveTwo × Ioo (-δ) δ) ≃ₜ W,
          (∀ (q : UnitTwoSphere) (t : Ioo (-δ) δ),
            (e (Quotient.mk realProjectiveTwoSetoid q, t)).val = f (q, u q + t.val)) ∧
          range (fun q : RealProjectiveTwo =>
            (e (q, ⟨0, neg_lt_zero.mpr hδ, hδ⟩)).val) =
              range (fun q : UnitTwoSphere => f (q, u q)) := by
  have hc : Continuous (fun q : UnitTwoSphere => f (q, u q)) :=
    hf.continuousOn.comp_continuous (continuous_id.prodMk hu)
      (fun q => ⟨mem_univ q, abs_lt.mp (hbound q)⟩)
  refine ⟨isCompact_range hc, isConnected_range hc, ?_⟩
  obtain ⟨q₀, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set UnitTwoSphere).Nonempty) hu.abs.continuousOn
  let δ := (s - |u q₀|) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr (hbound q₀))
  have hshift (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (-δ) δ) :
      u q + t ∈ Ioo (-s) s := by
    have hq : |u q| ≤ |u q₀| := hmax (mem_univ q)
    have hq₀ := hbound q₀
    have huq := abs_le.mp hq
    dsimp [δ] at ht
    constructor <;> linarith [ht.1, ht.2, huq.1, huq.2]
  let T : RoundCylinderSpace ≃ₜ RoundCylinderSpace := {
    toFun := fun z => (z.1, u z.1 + z.2)
    invFun := fun z => (z.1, z.2 - u z.1)
    left_inv := by intro z; simp
    right_inv := by intro z; simp
    continuous_toFun := continuous_fst.prodMk ((hu.comp continuous_fst).add continuous_snd)
    continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hu.comp continuous_fst)) }
  have hfT : IsLocalHomeomorphOn (f ∘ T) (univ ×ˢ Ioo (-δ) δ) :=
    hf.comp T.isLocalHomeomorph.isLocalHomeomorphOn
      (fun z hz => ⟨mem_univ _, hshift z.1 hz.2⟩)
  have hfiberT : ∀ z ∈ univ ×ˢ Ioo (-δ) δ, ∀ w ∈ univ ×ˢ Ioo (-δ) δ,
      (f ∘ T) z = (f ∘ T) w ↔ w = z ∨ w = (-z.1, z.2) := by
    intro z hz w hw
    rw [Function.comp_apply, Function.comp_apply,
      hfiber (T z) ⟨mem_univ _, hshift z.1 hz.2⟩
        (T w) ⟨mem_univ _, hshift w.1 hw.2⟩]
    constructor
    · rintro (heq | heq)
      · exact Or.inl (T.injective heq)
      · right
        have hq : w.1 = -z.1 := congrArg Prod.fst heq
        have ht : u w.1 + w.2 = u z.1 + z.2 := congrArg Prod.snd heq
        rw [hq, heven] at ht
        exact Prod.ext hq (add_left_cancel ht)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Prod.ext rfl (by change u (-z.1) + z.2 = u z.1 + z.2; rw [heven]))
  obtain ⟨hW, e, he⟩ := exists_projectiveCylinderSlab_homeomorph (f ∘ T) hfT hfiberT
  refine ⟨δ, hδ, (f ∘ T) '' (univ ×ˢ Ioo (-δ) δ), hW, ?_, e, he, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨T z, ⟨mem_univ _, hshift z.1 hz.2⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨q, rfl⟩ := Quotient.mk_surjective q
      refine ⟨q, ?_⟩
      have h := (he q ⟨0, neg_lt_zero.mpr hδ, hδ⟩).symm
      change f (q, u q + 0) = _ at h
      simpa only [add_zero] using h
    · rintro ⟨q, rfl⟩
      refine ⟨Quotient.mk realProjectiveTwoSetoid q, ?_⟩
      have h := he q ⟨0, neg_lt_zero.mpr hδ, hδ⟩
      change _ = f (q, u q + 0) at h
      simpa only [add_zero] using h

end PoincareConjecture
