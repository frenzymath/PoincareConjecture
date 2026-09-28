import PoincareConjecture.Proofs.M47.TerminalSourceCountableFlowPatch

set_option autoImplicit false

open Set Filter

universe u

namespace PoincareConjecture.M47

theorem terminalSourceCountable_composed_good_tail
    (j : ℕ) {Q : {a : ℕ // j ≤ a} → Prop}
    {sigma kappa : ℕ → ℕ}
    (hsigma : StrictMono sigma) (hkappa : StrictMono kappa)
    (hGood : ∀ᶠ a in Filter.comap
      (Subtype.val : {a : ℕ // j ≤ a} → ℕ) atTop, Q a) :
    ∀ᶠ k in atTop,
      ∃ hj : j ≤ sigma (kappa k),
        (∀ a : {a : ℕ // j ≤ a}, a.val = sigma (kappa k) → Q a) ∧
          terminalSourceCountableSourceIndex j (sigma (kappa k)) =
            ⟨sigma (kappa k), hj⟩ := by
  have hcomp : StrictMono (sigma ∘ kappa) := hsigma.comp hkappa
  have hto : Tendsto (sigma ∘ kappa) atTop atTop := hcomp.tendsto_atTop
  have hstage : ∀ᶠ k in atTop, j ≤ (sigma ∘ kappa) k :=
    hto.eventually (eventually_ge_atTop j)
  have hgood' : ∀ᶠ k in atTop,
      ∀ a : {l : ℕ // j ≤ l}, a.val = (sigma ∘ kappa) k → Q a :=
    hto.eventually (Filter.eventually_comap.mp hGood)
  filter_upwards [hstage, hgood'] with k hk hg
  refine ⟨hk, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hg
  · exact terminalSourceCountableSourceIndex_good hk

end PoincareConjecture.M47
