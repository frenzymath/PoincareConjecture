import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.ClosedCollarIntervalGeometry

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "I" => Icc (-1 : ℝ) 1

theorem half_collar_attachment
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : Set E} (hA : IsConnected A) (R : Set X) (c : E × ℝ → X)
    (hc : ContinuousOn c (A ×ˢ I)) (hi : InjOn c (A ×ˢ I))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1)
    (hR : MapsTo c (A ×ˢ Icc (-ε) ε) R) (positive : Bool) :
    let Q := R \ c '' (A ×ˢ Ioo (-ε) ε)
    let Qh := R \ c '' (A ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε))
    let D := c '' (A ×ˢ (if positive then Icc 0 ε else Icc (-ε) 0))
    Qh = Q ∪ D ∧ IsConnected D ∧
      Q ∩ D = c '' (A ×ˢ {if positive then ε else -ε}) ∧ (Q ∩ D).Nonempty := by
  let Q := R \ c '' (A ×ˢ Ioo (-ε) ε)
  let Qh := R \ c '' (A ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε))
  let D := c '' (A ×ˢ (if positive then Icc 0 ε else Icc (-ε) 0))
  have hsub : A ×ˢ Icc (-ε) ε ⊆ A ×ˢ I :=
    prod_mono subset_rfl (Icc_subset_Icc (neg_le_neg hεsmall) hεsmall)
  have hDsub : A ×ˢ (if positive then Icc 0 ε else Icc (-ε) 0) ⊆ A ×ˢ Icc (-ε) ε := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
      exact prod_mono subset_rfl (Icc_subset_Icc (by linarith) (by linarith))
  have hhalfsub : A ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε) ⊆ A ×ˢ Ioo (-ε) ε := by
    rintro z hz
    refine ⟨hz.1,?_⟩
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hz <;>
      constructor <;> linarith [hz.2.1,hz.2.2]
  have hDi : IsConnected (if positive then Icc (0 : ℝ) ε else Icc (-ε) 0) := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
      exact isConnected_Icc (by linarith)
  have hDc : IsConnected D := (hA.prod hDi).image c (hc.mono (hDsub.trans hsub))
  have hQheq : Qh = Q ∪ D := by
    apply Subset.antisymm
    · rintro x ⟨hxR,hxnot⟩
      by_cases hx : x ∈ c '' (A ×ˢ Ioo (-ε) ε)
      · right
        obtain ⟨z,hz,rfl⟩ := hx
        refine ⟨z,⟨hz.1,?_⟩,rfl⟩
        have htime : ¬ z.2 ∈ if positive then Ioo (-ε) 0 else Ioo 0 ε :=
          fun ht => hxnot ⟨z,⟨hz.1,ht⟩,rfl⟩
        cases positive <;> simp only [Bool.false_eq_true,reduceIte,mem_Ioo] at htime ⊢
        · exact ⟨hz.2.1.le,by by_contra h; exact htime ⟨lt_of_not_ge h,hz.2.2⟩⟩
        · exact ⟨by by_contra h; exact htime ⟨hz.2.1,lt_of_not_ge h⟩,hz.2.2.le⟩
      · exact Or.inl ⟨hxR,hx⟩
    · rintro x (hx | ⟨z,hz,rfl⟩)
      · exact ⟨hx.1,fun h => hx.2 (image_mono hhalfsub h)⟩
      · refine ⟨hR (hDsub hz),?_⟩
        rintro ⟨w,hw,heq⟩
        have hwfull := hhalfsub hw
        have hzw := hi (hsub ⟨hwfull.1,hwfull.2.1.le,hwfull.2.2.le⟩)
          (hsub (hDsub hz)) heq
        have ht := congrArg Prod.snd hzw
        cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hz hw <;>
          linarith [hz.2.1,hz.2.2,hw.2.1,hw.2.2]
  have hcontact : Q ∩ D = c '' (A ×ˢ {if positive then ε else -ε}) := by
    apply Subset.antisymm
    · rintro x ⟨hx,⟨z,hz,rfl⟩⟩
      refine ⟨z,⟨hz.1,?_⟩,rfl⟩
      have hnot : ¬ (-ε < z.2 ∧ z.2 < ε) := fun ht => hx.2 ⟨z,⟨hz.1,ht⟩,rfl⟩
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hz ⊢
      · change z.2 = -ε
        by_contra ht
        exact hnot ⟨lt_of_le_of_ne hz.2.1 (Ne.symm ht),by linarith [hz.2.2]⟩
      · change z.2 = ε
        by_contra ht
        exact hnot ⟨by linarith [hz.2.1],lt_of_le_of_ne hz.2.2 ht⟩
    · rintro _ ⟨z,hz,rfl⟩
      have htd : z.2 ∈ if positive then Icc 0 ε else Icc (-ε) 0 := by
        have ht : z.2 = if positive then ε else -ε := hz.2
        rw [ht]
        cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
          exact ⟨by linarith,by linarith⟩
      refine ⟨⟨hR (hDsub ⟨hz.1,htd⟩),?_⟩,⟨z,⟨hz.1,htd⟩,rfl⟩⟩
      rintro ⟨w,hw,heq⟩
      have hzw := hi (hsub ⟨hw.1,hw.2.1.le,hw.2.2.le⟩) (hsub (hDsub ⟨hz.1,htd⟩)) heq
      have ht := congrArg Prod.snd hzw
      have hztime : z.2 = if positive then ε else -ε := hz.2
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hztime <;>
        linarith [hw.2.1,hw.2.2]
  refine ⟨hQheq,hDc,hcontact,?_⟩
  obtain ⟨x,hx⟩ := hA.nonempty
  rw [hcontact]
  exact ⟨c (x,if positive then ε else -ε),⟨(x,if positive then ε else -ε),⟨hx,rfl⟩,rfl⟩⟩

end PoincareConjecture.M76
