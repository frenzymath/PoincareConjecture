import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.DifferentiatedEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergEuclidean

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def secondOrderOperator (a : E → Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → E → ℝ) (u : E → ℝ) : E → ℝ := fun x =>
  (∑ i, ∑ j, a x i j * partialDeriv i (partialDeriv j u) x) +
    ∑ i, b i x * partialDeriv i u x

def principalSource (a : E → Matrix (Fin d) (Fin d) ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => -(∑ i, partialDeriv i (matrixFlux a (fun j => partialDeriv j u) i) x)

theorem secondOrderOperator_eq_of_eventuallyEq
    (a : E → Matrix (Fin d) (Fin d) ℝ) (b : Fin d → E → ℝ)
    {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    secondOrderOperator a b u x = secondOrderOperator a b v x := by
  have hp (i : Fin d) : partialDeriv i u =ᶠ[𝓝 x] partialDeriv i v := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hy
  have hp₂ (i j : Fin d) : partialDeriv i (partialDeriv j u) x =
      partialDeriv i (partialDeriv j v) x :=
    congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) (hp j).fderiv_eq
  simp only [secondOrderOperator, hp₂, (hp _).self_of_nhds]

theorem secondOrderOperator_eqOn {V : Set E} (hV : IsOpen V)
    {a a' : E → Matrix (Fin d) (Fin d) ℝ} {b b' : Fin d → E → ℝ}
    (ha : EqOn a a' V) (hb : ∀ i, EqOn (b i) (b' i) V)
    {u v : E → ℝ} (hu : EqOn u v V) :
    EqOn (secondOrderOperator a b u) (secondOrderOperator a' b' v) V := by
  intro x hx
  have hg : u =ᶠ[𝓝 x] v := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hu hy
  rw [secondOrderOperator_eq_of_eventuallyEq a b hg]
  simp only [secondOrderOperator, ha hx, hb _ hx]

theorem iterate_secondOrderOperator_eqOn {V : Set E} (hV : IsOpen V)
    {a a' : E → Matrix (Fin d) (Fin d) ℝ} {b b' : Fin d → E → ℝ}
    (ha : EqOn a a' V) (hb : ∀ i, EqOn (b i) (b' i) V)
    {u v : E → ℝ} (hu : EqOn u v V) (j : ℕ) :
    EqOn ((secondOrderOperator a b)^[j] u) ((secondOrderOperator a' b')^[j] v) V := by
  induction j with
  | zero => exact hu
  | succ j ih =>
      simpa only [Function.iterate_succ_apply'] using secondOrderOperator_eqOn hV ha hb ih

theorem contDiff_secondOrderOperator
    {a : E → Matrix (Fin d) (Fin d) ℝ} {b : Fin d → E → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (secondOrderOperator a b u) := by
  apply ContDiff.add
  · exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (ha i j).mul (contDiff_partial (contDiff_partial hu j) i)
  · exact ContDiff.sum fun i _ => (hb i).mul (contDiff_partial hu i)

theorem weakEquation_principalSource {V : Set E} (hV : IsOpen V)
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    WeakEquation V (matrixFlux a (fun j => partialDeriv j u)) (principalSource a u) := by
  let F := matrixFlux a (fun j => partialDeriv j u)
  have hF (i) : ContDiff ℝ ∞ (F i) :=
    ContDiff.sum fun j _ => (ha i j).mul (contDiff_partial hu j)
  intro φ hφ hφc hφV
  have hi (i) := HasWeakPartialDeriv.of_contDiff (i := i) hV
    ((hF i).of_le (by simp)) φ hφ hφc hφV
  have hFi (i) : LocallyIntegrable (F i) (volume.restrict V) :=
    (hF i).continuous.locallyIntegrable.mono_measure Measure.restrict_le_self
  have hDi (i) : LocallyIntegrable (partialDeriv i (F i)) (volume.restrict V) :=
    (contDiff_partial (hF i) i).continuous.locallyIntegrable.mono_measure
      Measure.restrict_le_self
  change (∫ x in V, ∑ i, F i x * partialDeriv i φ x) =
    ∫ x in V, (-(∑ i, partialDeriv i (F i) x)) * φ x
  rw [integral_finsetSum _ (fun i _ => integrable_mul_partial_test (hFi i) hφ hφc i)]
  simp_rw [neg_mul, Finset.sum_mul]
  rw [integral_neg, integral_finsetSum _ (fun i _ => integrable_mul_test (hDi i) hφ hφc),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => hi i)

theorem principal_equation_of_smooth [NeZero d] {Ω V : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (hV : IsOpen V)
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, B.principalIntegrand u φ x) =
        ∫ x in V, principalSource B.a u x * φ x := by
  intro φ hφ hφc hφV
  have h := weakEquation_principalSource hV B.smooth_a hu φ hφ hφc hφV
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SmoothEllipticBilinearForm.principalIntegrand, matrixFlux,
    partialDeriv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [B.symm]

theorem principalSource_eq_secondOrderOperator
    {a : E → Matrix (Fin d) (Fin d) ℝ} (b : Fin d → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (x : E) :
    principalSource a u x = -secondOrderOperator a b u x +
      ∑ j, (b j x - ∑ i, partialDeriv i (fun y => a y i j) x) * partialDeriv j u x := by
  have hd (i j) : DifferentiableAt ℝ (fun y => a y i j * partialDeriv j u y) x :=
    ((ha i j).mul (contDiff_partial hu j)).differentiable (by simp) x
  have hprod (i j) : partialDeriv i (fun y => a y i j * partialDeriv j u y) x =
      a x i j * partialDeriv i (partialDeriv j u) x +
        partialDeriv i (fun y => a y i j) x * partialDeriv j u x := by
    change (fderiv ℝ (fun y => a y i j * partialDeriv j u y) x)
      (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_mul ((ha i j).differentiable (by simp) x)
      ((contDiff_partial hu j).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, partialDeriv]
    ring
  have hflux (i) : partialDeriv i (matrixFlux a (fun j => partialDeriv j u) i) x =
      ∑ j, (a x i j * partialDeriv i (partialDeriv j u) x +
        partialDeriv i (fun y => a y i j) x * partialDeriv j u x) := by
    change (fderiv ℝ (fun y => ∑ j, a y i j * partialDeriv j u y) x)
      (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_sum (fun j _ => hd i j)]
    simp only [sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hprod i j)
  unfold principalSource secondOrderOperator
  simp_rw [hflux, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm (f := fun j i =>
    partialDeriv i (fun y => a y i j) x * partialDeriv j u x)]
  ring

end Poincare.Analysis.Elliptic.InteriorEstimates
