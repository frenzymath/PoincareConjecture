import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Eigenfunction
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.TestCalculus

noncomputable section

open Set MeasureTheory Function Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace Poincare.Analysis.Elliptic

open Iteration Sobolev.Weak

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem integrable_mul_compact_test {O : Set E} {u ψ : E → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψO : tsupport ψ ⊆ O) :
    Integrable (fun x => u x * ψ x) (volume.restrict O) := by
  let : IsFiniteMeasure (volume.restrict (tsupport ψ)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hψc.measure_lt_top (μ := volume)⟩
  have huK : IntegrableOn u (tsupport ψ) :=
    (hu (tsupport ψ) hψc hψO).integrable (by norm_num)
  have hprod := huK.mul_continuousOn hψ.continuousOn hψc
  exact (hprod.integrable_of_forall_notMem_eq_zero
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])).integrableOn

theorem weakEquation_of_adjoint [NeZero n]
    {O : Set E} (hO : IsOpen O)
    (A : E → Matrix (Fin n) (Fin n) ℝ) (u : E → ℝ) (p : Fin n → E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hsymm : ∀ x ∈ O, ∀ i j, A x i j = A x j i)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (hadj : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * ∑ i, fderiv ℝ
        (fun y => ∑ j, A y i j * fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) = 0) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
  intro φ hφ hφc hφO
  let ψ : Fin n → E → ℝ := fun i x => ∑ j, A x i j * partialDeriv j φ x
  have hψ (i : Fin n) : ContDiff ℝ ∞ (ψ i) := by
    apply ContDiff.sum
    intro j _
    simpa only [mul_comm] using contDiff_cutoff_mul hO (contDiff_partial hφ j)
      (hA i j) ((tsupport_partial_subset j φ).trans hφO)
  have hψsupp (i : Fin n) : tsupport (ψ i) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hxφ
    apply hx
    change (∑ j, A x i j * partialDeriv j φ x) = 0
    apply Finset.sum_eq_zero
    intro j _
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => hxφ (tsupport_partial_subset j φ h)), mul_zero]
  have hψc (i : Fin n) : HasCompactSupport (ψ i) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) (hψsupp i)
  have hψO (i : Fin n) : tsupport (ψ i) ⊆ O := (hψsupp i).trans hφO
  have hleft (i : Fin n) : Integrable (fun x => u x * partialDeriv i (ψ i) x)
      (volume.restrict O) :=
    integrable_mul_compact_test hu (contDiff_partial (hψ i) i).continuous
      (hasCompactSupport_partial (hψc i) i) ((tsupport_partial_subset i (ψ i)).trans (hψO i))
  have hright (i : Fin n) : Integrable (fun x => p i x * ψ i x) (volume.restrict O) :=
    integrable_mul_compact_test (hp i) (hψ i).continuous (hψc i) (hψO i)
  have hibp (i : Fin n) : (∫ x in O, u x * partialDeriv i (ψ i) x) =
      -(∫ x in O, p i x * ψ i x) :=
    hpartial i (ψ i) (hψ i) (hψc i) (hψO i)
  have hzero := hadj φ hφ hφc hφO
  change (∫ x in O, u x * ∑ i, partialDeriv i (ψ i) x) = 0 at hzero
  simp_rw [Finset.mul_sum] at hzero
  rw [integral_finsetSum Finset.univ (fun i _ => hleft i)] at hzero
  simp_rw [hibp] at hzero
  rw [Finset.sum_neg_distrib] at hzero
  have hflux : (∫ x in O, ∑ i, p i x * ψ i x) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hright i)]
    exact neg_eq_zero.mp hzero
  calc
    (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, ∑ i, p i x * ψ i x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
      dsimp only [ψ, partialDeriv]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm x hx j i]
      ring
    _ = 0 := hflux

theorem contDiffOn_of_continuous_of_adjoint (hn : 0 < n)
    {O : Set E} (hO : IsOpen O) (A : E → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (u : E → ℝ) (hu : ContinuousOn u O) (p : Fin n → E → ℝ)
    (huL2 : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hpartial : ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * φ x))
    (hadj : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * ∑ i, fderiv ℝ
        (fun y => ∑ j, A y i j * fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) = 0) :
    ContDiffOn ℝ ∞ u O := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hsymm : ∀ x ∈ O, ∀ i j, A x i j = A x j i := by
    intro x hx i j
    simpa using (hpos x hx).isHermitian.apply j i
  have heq := weakEquation_of_adjoint hO A u p hA hsymm huL2 hp hpartial hadj
  obtain ⟨U, hU, hUu⟩ := exists_smooth_representative hn hO A (fun _ => 0) u p
    hA hpos contDiffOn_const huL2 hp hpartial (by
      intro φ hφ hφc hφO
      simpa only [zero_mul, integral_zero] using heq φ hφ hφc hφO)
  have heqOn := Measure.eqOn_open_of_ae_eq hUu hO hU.continuousOn hu
  exact hU.congr fun x hx => (heqOn hx).symm

end Poincare.Analysis.Elliptic
