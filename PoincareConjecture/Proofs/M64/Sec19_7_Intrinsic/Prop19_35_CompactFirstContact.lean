import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FirstContactNormals

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_compact_first_contact
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (f : X → AnnulusCoordinates) (hf : Continuous f)
    (hlocal : ∀ x : X, ∃ U ∈ 𝓝 x, InjOn f U)
    (height : X → ℝ) (hh : Continuous height) (hfail : ¬Function.Injective f) :
    ∃ p q : X, p ≠ q ∧ f p = f q ∧
      InjOn f {x | height x < max (height p) (height q)} := by
  let C : Set (X × X) := {z | f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hC : IsClosed C := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    change ¬(f z.1 = f z.2 ∧ z.1 ≠ z.2) at hz
    by_cases hmeet : f z.1 = f z.2
    · have heq : z.1 = z.2 := by tauto
      obtain ⟨U, hU, hi⟩ := hlocal z.1
      have hU' : U ∈ 𝓝 z.2 := heq ▸ hU
      have hfirst : ∀ᶠ w : X × X in 𝓝 z, w.1 ∈ U := continuous_fst.continuousAt hU
      have hsecond : ∀ᶠ w : X × X in 𝓝 z, w.2 ∈ U := continuous_snd.continuousAt hU'
      filter_upwards [hfirst, hsecond] with w hw1 hw2
      change ¬(f w.1 = f w.2 ∧ w.1 ≠ w.2)
      rintro ⟨hw, hne⟩
      exact hne (hi hw1 hw2 hw)
    · have hne : ∀ᶠ w : X × X in 𝓝 z, f w.1 ≠ f w.2 :=
        (isOpen_ne_fun (hf.comp continuous_fst) (hf.comp continuous_snd)).mem_nhds hmeet
      filter_upwards [hne] with w hw
      exact fun hc => hw hc.1
  have hnonempty : C.Nonempty := by
    rw [Function.Injective] at hfail
    push Not at hfail
    obtain ⟨p, q, heq, hne⟩ := hfail
    exact ⟨(p, q), heq, hne⟩
  have hmax : Continuous (fun z : X × X => max (height z.1) (height z.2)) :=
    (hh.comp continuous_fst).max (hh.comp continuous_snd)
  obtain ⟨z, hz, hmin⟩ := hC.isCompact.exists_isMinOn hnonempty hmax.continuousOn
  refine ⟨z.1, z.2, hz.2, hz.1, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hbound := hmin (show (x, y) ∈ C from ⟨hxy, hne⟩)
  change max (height z.1) (height z.2) ≤ max (height x) (height y) at hbound
  change height x < max (height z.1) (height z.2) at hx
  change height y < max (height z.1) (height z.2) at hy
  exact (not_le_of_gt (max_lt hx hy)) hbound

end PoincareConjecture
