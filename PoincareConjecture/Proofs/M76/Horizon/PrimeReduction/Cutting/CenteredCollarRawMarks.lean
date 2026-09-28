import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCollarProduct

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_centered_collar_raw_marks
    {A X : Type*} [TopologicalSpace A] [T2Space A]
    [TopologicalSpace X] [T2Space X]
    {N : Set A} (hN : IsCompact N) (c : A × ℝ → X)
    (hc : ContinuousOn c (N ×ˢ Icc (-1 : ℝ) 1))
    (hi : InjOn c (N ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1) {S : Set X}
    (hS : S = c '' (N ×ˢ ({0} : Set ℝ))) :
    let O := c '' (N ×ˢ Ioo (-ε) ε)
    ∃ W : (N × unitInterval) ≃ₜ closure O,
      (∀ z, (W z : X) = c (z.1,(2 * (z.2 : ℝ) - 1) * ε)) ∧
      (∀ z, (W z : X) ∈ O ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1 / 2) ∧ S ⊆ closure O := by
  let O := c '' (N ×ˢ Ioo (-ε) ε)
  have hclosure : closure O = c '' (N ×ˢ Icc (-ε) ε) :=
    hc.closure_image_collar_strip hN hε hεsmall
  obtain ⟨W₀,hW₀⟩ := exists_closed_collar_product hN c hc hi hε hεsmall
  let W := W₀.trans (Homeomorph.setCongr hclosure.symm)
  have hval (z : N × unitInterval) :
      (W z : X) = c (z.1,(2 * (z.2 : ℝ) - 1) * ε) := hW₀ z
  have hfull (z : N × unitInterval) :
      ((z.1 : A),(2 * (z.2 : ℝ) - 1) * ε) ∈ N ×ˢ Icc (-1 : ℝ) 1 := by
    refine ⟨z.1.property,?_,?_⟩ <;> nlinarith [z.2.property.1,z.2.property.2]
  refine ⟨W,hval,?_,?_,?_⟩
  · intro z
    rw [hval]
    constructor
    · rintro ⟨w,hw,heq⟩
      have hwfull : w ∈ N ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨hw.1,by linarith [hw.2.1],by linarith [hw.2.2]⟩
      have ht := congrArg Prod.snd (hi hwfull (hfull z) heq)
      dsimp at ht
      constructor <;> nlinarith [hw.2.1,hw.2.2]
    · intro hz
      exact ⟨((z.1 : A),(2 * (z.2 : ℝ) - 1) * ε),
        ⟨z.1.property,by nlinarith [hz.1],by nlinarith [hz.2]⟩,rfl⟩
  · intro z
    rw [hval,hS]
    constructor
    · rintro ⟨w,hw,heq⟩
      have hw0 : w.2 = 0 := hw.2
      have hwfull : w ∈ N ×ˢ Icc (-1 : ℝ) 1 := ⟨hw.1,by rw [hw0]; norm_num⟩
      have ht := congrArg Prod.snd (hi hwfull (hfull z) heq)
      dsimp at ht
      nlinarith
    · intro hz
      refine ⟨((z.1 : A),0),⟨z.1.property,rfl⟩,?_⟩
      simp only [hz]
      congr 1
      ext
      · rfl
      · ring
  · rw [hS,hclosure]
    exact image_mono (prod_mono subset_rfl (by
      intro t ht
      have ht0 : t = 0 := ht
      rw [ht0]
      exact ⟨by linarith,hε.le⟩))

end PoincareConjecture.M76
