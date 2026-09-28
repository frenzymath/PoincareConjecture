import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LocalHeatTests
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem schwartz_eqOn_of_local_tests {O : Set V} (hO : IsOpen O)
    (X Y : 𝓢(V, ℝ))
    (htest : ∀ φ : 𝓢(V, ℝ), HasCompactSupport φ → tsupport φ ⊆ O →
      inner ℝ (φ.toLp 2 volume) (X.toLp 2 volume) =
        inner ℝ (φ.toLp 2 volume) (Y.toLp 2 volume)) :
    EqOn (X : V → ℝ) Y O := by
  have hc : Continuous (fun x => X x - Y x) := X.continuous.sub Y.continuous
  have hae : ∀ᵐ x ∂volume, x ∈ O → X x - Y x = 0 := by
    apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrable.locallyIntegrableOn O)
    intro φ hφ hcomp hφO
    have he := htest (hcomp.toSchwartzMap hφ) hcomp hφO
    rw [inner_schwartzToLp, inner_schwartzToLp] at he
    have hX : Integrable (fun x => φ x * X x) :=
      (hφ.continuous.mul X.continuous).integrable_of_hasCompactSupport hcomp.mul_right
    have hY : Integrable (fun x => φ x * Y x) :=
      (hφ.continuous.mul Y.continuous).integrable_of_hasCompactSupport hcomp.mul_right
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub hX hY]
    exact sub_eq_zero.mpr he
  have he : EqOn (fun x => X x - Y x) (fun _ => (0 : ℝ)) O :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hO.measurableSet).mpr hae)
      hO hc.continuousOn continuousOn_const
  exact fun x hx => sub_eq_zero.mp (he hx)

theorem raw_weak_heat_pointwise {K O : Set V} (hK : IsClosed K) (hO : IsOpen O)
    (hOK : O ⊆ K) {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (χ : 𝓢(V, ℝ)) (hχO : ∀ x ∈ O, χ x = 1)
    (W Z : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) Z) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator D hK η hη W) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z W)
    (X Y : Fin n → supportedTests K)
    (hX : ∀ j, (X j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (W j))
    (hY : ∀ j, (Y j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (Z j)) :
    ∀ x ∈ O, schwartzField (fun j => (Y j : 𝓢(V, ℝ))) x =
      @Add.add V inferInstance
        (fieldTraceHessian D (schwartzField (fun j => (X j : 𝓢(V, ℝ)))) x)
        (RicciFlow.ricciSharp D x (schwartzField (fun j => (X j : 𝓢(V, ℝ))) x)) := by
  classical
  let H := vectorTestGenerator hK (rawCutoffPrincipalCoefficient g η hη)
    (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) X
  have hcoord (k : Fin n) : EqOn (Y k : V → ℝ) (H k : V → ℝ) O := by
    apply schwartz_eqOn_of_local_tests hO (Y k) (H k)
    intro φ _hφ hφO
    let E := tsupport φ
    have hEK : E ⊆ K := hφO.trans hOK
    let p : supportedTests E := ⟨φ, fun x hx => image_eq_zero_of_notMem_tsupport hx⟩
    let f : Fin n → supportedTests E := fun j => if j = k then p else 0
    have hh := raw_weak_heat_local_test hK (isClosed_tsupport φ) hEK D η hη hηK χ
      (fun x hx => hχO x (hφO hx)) W Z heq X Y hX hY f
    have hpair (F : Fin n → supportedTests K) :
        inner ℝ (vectorTestValue K (fun j => supportedTestInclusion hEK (f j)))
          (vectorTestValue K F) =
            inner ℝ (φ.toLp 2 volume) ((F k : 𝓢(V, ℝ)).toLp 2 volume) := by
      simp only [PiLp.inner_apply, vectorTestValue]
      rw [Finset.sum_eq_single k]
      · simp only [f, if_pos rfl]
        rfl
      · intro j _ hj
        have hzero : supportedTestInclusion hEK (f j) = 0 := by
          apply Subtype.ext
          simp only [f, if_neg hj]
          rfl
        rw [hzero, map_zero, inner_zero_left]
      · simp
    exact (hpair Y).symm.trans (hh.trans (hpair H))
  intro x hx
  apply PiLp.ext
  intro k
  rw [schwartzField_apply (fun j => (Y j : 𝓢(V, ℝ)))]
  change (Y k : 𝓢(V, ℝ)) x = _
  exact (hcoord k hx).trans (raw_vectorTestGenerator_geometric hK D η hη hηK X x k)

end PoincareConjecture.M35.Uniqueness.Heat
