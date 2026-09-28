import PoincareConjecture.Proofs.M47.TerminalSourceCountableComposedTail









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

variable (j : ℕ) (M : {k : ℕ // j ≤ k} → Type u)
  [∀ a, TopologicalSpace (M a)] [∀ a, ChartedSpace E (M a)]
  [∀ a, IsManifold (𝓡 3) ∞ (M a)]
  {tau R : ℝ} (htau : 0 < tau)
  (F : ∀ a, RicciFlow 3 (M a) (Icc (-tau) 0))
  (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)



theorem terminalSourceCountable_composed_compatibility
    (f0 : ℕ → E → V) {Q : {a : ℕ // j ≤ a} → Prop}
    {sigma kappa : ℕ → ℕ}
    (hsigma : StrictMono sigma) (hkappa : StrictMono kappa)
    (hGood : ∀ᶠ a in Filter.comap
      (Subtype.val : {a : ℕ // j ≤ a} → ℕ) atTop, Q a) :
    ∀ᶠ k in atTop,
      ∃ hj : j ≤ sigma (kappa k),
        terminalSourceCountableSourceIndex j (sigma (kappa k)) =
            ⟨sigma (kappa k), hj⟩ ∧
        (∀ a : {a : ℕ // j ≤ a}, a.val = sigma (kappa k) → Q a) ∧
        (fun z : ℝ × E =>
          ((terminalSourceCountableSourceFlow j M htau F
            (sigma (kappa k))).metric z.1).pullbackCoefficients
            (C (terminalSourceCountableSourceIndex j (sigma (kappa k)))).chart
            z.2) =
          terminalSourceCountableNegative j M F C f0 (sigma (kappa k)) := by
  have htail := terminalSourceCountable_composed_good_tail j hsigma hkappa hGood
  have hcoeff := terminalSourceCountableSourceFlow_eventually_coefficients
    j M htau F C f0 (hsigma.comp hkappa)
  filter_upwards [htail, hcoeff] with k hk hflow
  obtain ⟨hj, hQ, hindex⟩ := hk
  refine ⟨hj, hindex, hQ, ?_⟩
  simpa only [Function.comp_apply] using hflow

end PoincareConjecture.M47
