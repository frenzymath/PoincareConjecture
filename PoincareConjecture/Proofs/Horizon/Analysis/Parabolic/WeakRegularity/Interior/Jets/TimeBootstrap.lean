import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.TimeSpatialJetAlgebra
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialTimeDerivative

open Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem exists_forced_time_spatial_weak_derivative
    {n m k : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u f : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m (k + 2) u)
    (hf : HasTimeSpatialL2Jet U m k f)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y) :
    ∃ T : Spacetime n → ℝ, HasTimeSpatialL2Jet U m k T ∧
      ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        (∫ y in U, φ y * T y) = -(∫ y in U, timeDeriv φ y * u y) := by
  obtain ⟨g, hg, hgw⟩ := hu.exists_spatial_derivatives hU
  choose A hA hAw using fun j => (hg j).exists_spatial_derivatives hU
  let H (i j : Fin n) := A j i
  have hHJ (i j : Fin n) : HasTimeSpatialL2Jet U m k (H i j) := hA j i
  let T (y : Spacetime n) : ℝ := f y +
    (∑ i, ∑ j, C.principal i j y * H i j y) -
    (∑ i, C.drift i y * g i y) - C.zeroth y * u y
  have hprincipal (i j : Fin n) : HasTimeSpatialL2Jet U m k
      (fun y => C.principal i j y * H i j y) :=
    (hHJ i j).mul_smooth hU (contDiffOn_univ.mp (hC.1 i j)) (hprincipalc i j)
  have hdrift (i : Fin n) : HasTimeSpatialL2Jet U m k
      (fun y => C.drift i y * g i y) :=
    (hg i).lower_spatial.mul_smooth hU (contDiffOn_univ.mp (hC.2.1 i)) (hdriftc i)
  have hzero : HasTimeSpatialL2Jet U m k (fun y => C.zeroth y * u y) :=
    (hu.of_spatial_le (by omega : k ≤ k + 2)).mul_smooth hU
      (contDiffOn_univ.mp hC.2.2) hzerothc
  have hT : HasTimeSpatialL2Jet U m k T :=
    ((hf.add (HasTimeSpatialL2Jet.sum Finset.univ
      (fun i _ => HasTimeSpatialL2Jet.sum Finset.univ (fun j _ => hprincipal i j)))).sub
        (HasTimeSpatialL2Jet.sum Finset.univ (fun i _ => hdrift i))).sub hzero
  refine ⟨T, hT, ?_⟩
  intro φ hφ hφc hφU
  have hCU : C.IsSmoothOn U :=
    ⟨fun i j => (hC.1 i j).mono (subset_univ U),
      fun i => (hC.2.1 i).mono (subset_univ U), hC.2.2.mono (subset_univ U)⟩
  exact weak_time_pairing_of_forcing hU hCU hu.locallyIntegrableOn hf.locallyIntegrableOn
    (fun i => (hg i).locallyIntegrableOn) (fun i j => (hHJ i j).locallyIntegrableOn)
    hforce hgw (fun i j => hAw j i) hφ hφc hφU

theorem time_spatial_jet_of_spatial_jet_and_weak_equation
    {n m k : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u : Spacetime n → ℝ} (hu : HasSpatialL2Jet U (k + 2 * m) u)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = 0) :
    HasTimeSpatialL2Jet U m k u := by
  induction m generalizing k with
  | zero => simpa only [HasTimeSpatialL2Jet, Nat.mul_zero, Nat.add_zero] using hu
  | succ m ih =>
    have hu' : HasSpatialL2Jet U ((k + 2) + 2 * m) u := by
      convert hu using 1 <;> omega
    have hureg : HasTimeSpatialL2Jet U m (k + 2) u := ih hu'
    have hforced (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
        (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
        (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * (0 : ℝ) := by
      simpa only [mul_zero, integral_zero] using hforce φ hφ hφc hφU
    obtain ⟨T, hT, hTw⟩ := exists_forced_time_spatial_weak_derivative
      hU hC hprincipalc hdriftc hzerothc hureg (HasTimeSpatialL2Jet.zero U m k) hforced
    exact ⟨hu.of_le (by omega), T, hT, hTw⟩

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
