import PoincareConjecture.Proofs.M14.Sec6_3_InitialJacobiDerivative
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiAnyTime
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPackaging
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackZeroField










set_option autoImplicit false

open Set
open scoped Manifold

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}

private theorem horizontal_transport_zero {q r : G.Point} (h : q = r) :
    (h ▸ (0 : G.Horizontal q) : G.Horizontal r) = 0 := by
  cases h
  rfl



theorem initialValuePath_differential_zero_direction
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) (s : ℝ) :
    (initialValuePath_differentialData hM04 hM12 P 0).field s = 0 := by
  change initialValuePath_differentialField hM04 hM12 P 0 s = 0
  unfold initialValuePath_differentialField
  split_ifs with hs
  · rw [map_zero]
    exact horizontal_transport_zero _
  · rfl



theorem initialValuePath_differential_zero_direction_derivative
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval 0 τ) :
    M14JacobiFirstDerivative (initialValuePath_differentialData hM04 hM12 P 0) s = 0 :=
  horizontalCovariantDerivative_zero_field
    (initialValuePath_differentialData hM04 hM12 P 0).extension
    (fun r _ => initialValuePath_differential_zero_direction hM04 hM12 P r) hs
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt P.path.tau_nonneg P.path.tau_lt) s hs)
    (((P.square_path.smooth.mono P.square_path.interval_subset) s hs).mdifferentiableWithinAt
      (by simp))




theorem initialValuePath_direction_eq_zero_of_phase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) (W : G.Horizontal x) {c : ℝ}
    (hc : c ∈ M14SqrtParameterInterval 0 τ)
    (hfield : (initialValuePath_differentialData hM04 hM12 P W).field c = 0)
    (hderiv : M14JacobiFirstDerivative (initialValuePath_differentialData hM04 hM12 P W) c = 0) :
    W = 0 := by
  let Q := initialValuePath_differentialData hM04 hM12 P W
  let Q₀ := initialValuePath_differentialData hM04 hM12 P 0
  have hQ := jacobiField_isHorizontalJacobiPair Q
    (fun _ hs => initialValuePath_differential_jacobi hM04 hM12 P W hs)
  have hQ₀ := jacobiField_isHorizontalJacobiPair Q₀
    (fun _ hs => initialValuePath_differential_jacobi hM04 hM12 P 0 hs)
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ :=
    ⟨by simp, Real.sqrt_nonneg _⟩
  have hphase := horizontalJacobiPair_unique_at P.square_path hM04 hM12 hQ hQ₀ hc
    (Prod.ext (hfield.trans (initialValuePath_differential_zero_direction hM04 hM12 P c).symm)
      (hderiv.trans (initialValuePath_differential_zero_direction_derivative hM04 hM12 P hc).symm))
    0 hzero
  have hD : M14JacobiFirstDerivative Q 0 = 0 :=
    (congrArg Prod.snd hphase).trans
      (initialValuePath_differential_zero_direction_derivative hM04 hM12 P hzero)
  obtain ⟨hbase, hW⟩ := initialValuePath_differential_initialDerivative hM04 hM12 P W
  change hbase ▸ M14JacobiFirstDerivative Q 0 = (2 : ℝ) • W at hW
  rw [hD, horizontal_transport_zero] at hW
  exact (smul_eq_zero.mp hW.symm).resolve_left (by norm_num)

end PoincareConjecture.M14
