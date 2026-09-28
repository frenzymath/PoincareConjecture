import PoincareConjecture.Proofs.M14.Mathlib.ContinuousFirstExit










set_option autoImplicit false

open Set

namespace PoincareConjecture.Proofs.M46




theorem exists_last_entry_of_continuousOn {X : Type*} [TopologicalSpace X]
    {gamma : ℝ → X} {a b : ℝ} (hab : a < b)
    (hgamma : ContinuousOn gamma (Icc a b))
    {O : Set X} (hO : IsOpen O) (ha : gamma a ∉ O) (hb : gamma b ∈ O) :
    ∃ c ∈ Ico a b, gamma c ∉ O ∧ MapsTo gamma (Ioc c b) O ∧
      MapsTo gamma (Icc c b) (closure O) := by
  let reflection : ℝ → ℝ := fun t => a + b - t
  have hreflect : MapsTo reflection (Icc a b) (Icc a b) := by
    intro t ht
    dsimp only [reflection]
    constructor <;> linarith [ht.1, ht.2]
  have ha' : (gamma ∘ reflection) a ∈ O := by
    simpa only [Function.comp_apply, reflection, add_sub_cancel_left] using hb
  have hb' : (gamma ∘ reflection) b ∉ O := by
    simpa only [Function.comp_apply, reflection, add_sub_cancel_right] using ha
  obtain ⟨c, hc, hout, hinside, hclosure⟩ := M14.exists_first_exit_of_continuousOn
    (hgamma.comp (continuous_const.sub continuous_id).continuousOn hreflect) hO ha'
    ⟨b, ⟨hab.le, le_rfl⟩, hb'⟩
  refine ⟨a + b - c, ⟨by linarith [hc.2], by linarith [hc.1]⟩, hout, ?_, ?_⟩
  · intro t ht
    have hrt : reflection t ∈ Ico a c := by
      dsimp only [reflection]
      constructor <;> linarith [ht.1, ht.2]
    have h := hinside hrt
    change gamma (a + b - (a + b - t)) ∈ O at h
    simpa only [sub_sub_cancel] using h
  · intro t ht
    have hrt : reflection t ∈ Icc a c := by
      dsimp only [reflection]
      constructor <;> linarith [ht.1, ht.2]
    have h := hclosure hrt
    change gamma (a + b - (a + b - t)) ∈ closure O at h
    simpa only [sub_sub_cancel] using h

end PoincareConjecture.Proofs.M46
