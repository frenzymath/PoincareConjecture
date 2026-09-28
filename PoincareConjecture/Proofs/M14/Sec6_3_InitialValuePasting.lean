import PoincareConjecture.Proofs.M14.Sec6_3_EulerOverlap
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurvePath
import PoincareConjecture.Proofs.M14.Mathlib.ClosedCurvePasting
import PoincareConjecture.Definitions.M14Exponential











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ σ τ' : ℝ} {x y x' y' : G.Point} {Z : G.Horizontal x}





theorem exists_initialValuePath_of_overlap (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z)
    {q : M14BackwardPath G T σ τ' x' y'} (S : M14SquareRootPath G q)
    (F : M14PullbackExtension G S.curve (M14SqrtParameterInterval σ τ')
      S.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval σ τ', ∀ W,
      M14SquareRootEulerResidual G S F s W = 0)
    (hστ : σ < τ) (hττ' : τ < τ')
    (heq : EqOn P.square_path.curve S.curve (M14SqrtParameterInterval σ τ)) :
    ∃ z : G.Point, ∃ Q : M14SquareRootInitialValuePath G T τ' x z Z,
      EqOn Q.square_path.curve P.square_path.curve (M14SqrtParameterInterval 0 τ) ∧
      EqOn Q.square_path.curve S.curve (M14SqrtParameterInterval σ τ') := by
  let α := fun s => if s ≤ Real.sqrt τ then P.square_path.curve s else S.curve s
  have hτ : 0 < τ := P.path.tau_lt
  have hτ' : 0 < τ' := hτ.trans hττ'
  have hlc : Real.sqrt σ < Real.sqrt τ := Real.sqrt_lt_sqrt q.tau_nonneg hστ
  have hleft : EqOn α P.square_path.curve (M14SqrtParameterInterval 0 τ) :=
    fun s hs => if_pos hs.2
  have hright : EqOn α S.curve (M14SqrtParameterInterval σ τ') := by
    intro s hs
    by_cases hsc : s ≤ Real.sqrt τ
    · exact (if_pos hsc).trans (heq ⟨hs.1, hsc⟩)
    · exact if_neg hsc
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α
      (M14SqrtParameterInterval 0 τ') :=
    contMDiffOn_paste_closed_intervals (spacetimeModel n) hlc
      (P.square_path.smooth.mono P.square_path.interval_subset)
      (S.smooth.mono S.interval_subset) heq
  have hclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 τ') :
      G.spacetime.timeFunction (α s) = T - s ^ 2 := by
    by_cases hsc : s ≤ Real.sqrt τ
    · rw [hleft ⟨hs.1, hsc⟩]
      exact P.square_path.curve_time s ⟨hs.1, hsc⟩
    · have hsl : Real.sqrt σ ≤ s := hlc.le.trans (le_of_not_ge hsc)
      rw [hright ⟨hsl, hs.2⟩]
      exact S.curve_time s ⟨hsl, hs.2⟩
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ := by
    exact ⟨by simp only [Real.sqrt_zero, le_refl], Real.sqrt_nonneg τ⟩
  obtain ⟨hP₀, hv₀⟩ := P.initial_velocity
  have hstart : α (Real.sqrt 0) = x := by
    rw [Real.sqrt_zero, hleft hzero, hP₀]
  let p₀ := backwardPathOfSquareCurve hM12 le_rfl hτ' α hα hclock
  let R₀ := squareRootPathOfSquareCurve hM12 le_rfl hτ' α hα hclock
  let p : M14BackwardPath G T 0 τ' x (α (Real.sqrt τ')) :=
    { p₀ with
      base_time := P.path.base_time
      curve_start := p₀.curve_start.trans hstart }
  let R : M14SquareRootPath G p := { R₀ with curve := R₀.curve }
  have hR (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 τ') : R.curve s = α s :=
    squareRootPathOfSquareCurve_curve hM12 le_rfl hτ' α hα hclock hs
  have hsubL : M14SqrtParameterInterval 0 τ ⊆ M14SqrtParameterInterval 0 τ' :=
    Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hττ'.le)
  have hsubR : M14SqrtParameterInterval σ τ' ⊆ M14SqrtParameterInterval 0 τ' :=
    Icc_subset_Icc (Real.sqrt_le_sqrt q.tau_nonneg) le_rfl
  have hRL : EqOn R.curve P.square_path.curve (M14SqrtParameterInterval 0 τ) :=
    fun s hs => (hR s (hsubL hs)).trans (hleft hs)
  have hRR : EqOn R.curve S.curve (M14SqrtParameterInterval σ τ') :=
    fun s hs => (hR s (hsubR hs)).trans (hright hs)
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  have hE : ∀ s ∈ M14SqrtParameterInterval 0 τ', ∀ W,
      M14SquareRootEulerResidual G R E s W = 0 := by
    intro s hs W
    by_cases hsc : s ≤ Real.sqrt τ
    · have hsL : s ∈ M14SqrtParameterInterval 0 τ := ⟨hs.1, hsc⟩
      let W' : G.Horizontal (P.square_path.curve s) := hRL hsL ▸ W
      have hW : HEq W W' := (eqRec_heq _ _).symm
      rw [squareRootEulerResidual_eq_on_subset R P.square_path E P.extension hsubL
        Subset.rfl (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt le_rfl hτ)) hRL hsL hW]
      exact P.euler s hsL W'
    · have hsR : s ∈ M14SqrtParameterInterval σ τ' :=
        ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩
      let W' : G.Horizontal (S.curve s) := hRR hsR ▸ W
      have hW : HEq W W' := (eqRec_heq _ _).symm
      rw [squareRootEulerResidual_eq_on_subset R S E F hsubR Subset.rfl
        (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt q.tau_nonneg q.tau_lt)) hRR hsR hW]
      exact hEuler s hsR W'
  have hR₀ : R.curve 0 = x := (hRL hzero).trans hP₀
  have hv : hR₀ ▸ R.horizontal_velocity 0 = (2 : ℝ) • Z := by
    have hvel := squareRoot_horizontalVelocity_heq_on_subset R P.square_path hsubL
      Subset.rfl hRL hzero (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt le_rfl hτ) 0 hzero)
    have htrans : HEq (hR₀ ▸ R.horizontal_velocity 0) (R.horizontal_velocity 0) :=
      eqRec_heq _ _
    have hold : HEq (P.square_path.horizontal_velocity 0)
        (hP₀ ▸ P.square_path.horizontal_velocity 0) :=
      (eqRec_heq _ _).symm
    exact eq_of_heq ((htrans.trans hvel).trans (hold.trans (heq_of_eq hv₀)))
  exact ⟨_, ⟨p, R, E, hE, hR₀, hv⟩, hRL, hRR⟩

end PoincareConjecture.M14
