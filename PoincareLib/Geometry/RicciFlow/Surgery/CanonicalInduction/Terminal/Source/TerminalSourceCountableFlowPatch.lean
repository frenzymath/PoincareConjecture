import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Source.TerminalSourceCountableNegative

/-!
# Genuine source flows at every countable index

The selected source at max(k,j) supplies every early flow index. On
the good tail its full coefficients are exactly the original ones.
Only time restriction is used; the metric and connection are retained.
MT Proposition 5.14; terminal-source-countable-germs.md, A.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

/-- Every index selects one genuine source from the original good-index family. -/
def terminalSourceCountableSourceIndex (j k : ℕ) : {m : ℕ // j ≤ m} :=
  ⟨max k j, le_max_right k j⟩

/-- Available indices retain the literal original source index. -/
theorem terminalSourceCountableSourceIndex_good {j k : ℕ} (hjk : j ≤ k) :
    terminalSourceCountableSourceIndex j k = ⟨k, hjk⟩ := by
  apply Subtype.ext
  exact max_eq_left hjk

variable (j : ℕ) (M : {k : ℕ // j ≤ k} → Type u)
  [∀ a, TopologicalSpace (M a)] [∀ a, ChartedSpace E (M a)]
  [∀ a, IsManifold (𝓡 3) ∞ (M a)]
  {tau R : ℝ} (htau : 0 < tau)
  (F : ∀ a, RicciFlow 3 (M a) (Icc (-tau) 0))

/-- The actual selected source flow restricted to its buffered included interval. -/
noncomputable def terminalSourceCountableSourceFlow (k : ℕ) :
    RicciFlow 3 (M (terminalSourceCountableSourceIndex j k)) (Icc (-(tau / 4)) 0) where
  metric := (F (terminalSourceCountableSourceIndex j k)).metric
  connection := (F (terminalSourceCountableSourceIndex j k)).connection
  interval := ordConnected_Icc
  nontrivial := ⟨-(tau / 4), ⟨le_rfl, by linarith⟩, 0,
    ⟨by linarith, le_rfl⟩, by linarith⟩
  smooth := (F (terminalSourceCountableSourceIndex j k)).smooth.mono
    (prod_mono (fun _ hs => ⟨by linarith [hs.1], hs.2⟩) (Subset.refl _))
  equation := fun t ht x v w =>
    ((F (terminalSourceCountableSourceIndex j k)).equation t
      ⟨by linarith [ht.1], ht.2⟩ x v w).mono
        (fun _ hs => ⟨by linarith [hs.1], hs.2⟩)

/-- The restriction retains the full actual metric representative. -/
theorem terminalSourceCountableSourceFlow_metric (k : ℕ) :
    (terminalSourceCountableSourceFlow j M htau F k).metric =
      (F (terminalSourceCountableSourceIndex j k)).metric := rfl

variable (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)

/-- On a good index the patched flow has the full original coefficient function. -/
theorem terminalSourceCountableSourceFlow_coefficients_good
    (f0 : ℕ → E → V) {k : ℕ} (hjk : j ≤ k) :
    (fun z : ℝ × E =>
      ((terminalSourceCountableSourceFlow j M htau F k).metric z.1).pullbackCoefficients
        (C (terminalSourceCountableSourceIndex j k)).chart z.2) =
      terminalSourceCountableNegative j M F C f0 k := by
  rw [terminalSourceCountableNegative_good j M F C f0 hjk]
  change (fun z : ℝ × E =>
    ((F (terminalSourceCountableSourceIndex j k)).metric z.1).pullbackCoefficients
      (C (terminalSourceCountableSourceIndex j k)).chart z.2) = _
  rw [terminalSourceCountableSourceIndex_good hjk]

/-- Every further strict subsequence retains these same full coefficient functions. -/
theorem terminalSourceCountableSourceFlow_eventually_coefficients
    (f0 : ℕ → E → V) {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) :
    ∀ᶠ k in atTop,
      (fun z : ℝ × E =>
        ((terminalSourceCountableSourceFlow j M htau F (sigma k)).metric z.1).pullbackCoefficients
          (C (terminalSourceCountableSourceIndex j (sigma k))).chart z.2) =
        terminalSourceCountableNegative j M F C f0 (sigma k) := by
  filter_upwards [hsigma.tendsto_atTop.eventually (eventually_ge_atTop j)] with k hk
  exact terminalSourceCountableSourceFlow_coefficients_good j M htau F C f0 hk

end PoincareMT.M47
