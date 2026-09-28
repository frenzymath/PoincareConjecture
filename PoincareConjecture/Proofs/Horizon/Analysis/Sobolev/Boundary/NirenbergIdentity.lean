import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.TangentialTests
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Substitution.WeakEquation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak NirenbergStandardTest
open Poincare.Analysis.Elliptic
open NirenbergCrossBoundsNonSmooth

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem shift_mem_halfSpace (k : Fin d) (hk : k ≠ 0) (h : ℝ) {x : E}
    (hx : x ∈ halfSpace d) : x + h • EuclideanSpace.single k 1 ∈ halfSpace d := by
  simpa [halfSpace, PiLp.add_apply, PiLp.smul_apply, hk.symm] using hx

private theorem diffQuot_eqOn_halfSpace {u v : E → ℝ}
    (huv : EqOn u v (halfSpace d)) (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    EqOn (diffQuot k h u) (diffQuot k h v) (halfSpace d) := by
  intro x hx
  by_cases hh : h = 0
  · simp [hh]
  · rw [diffQuot_apply_of_ne k hh, diffQuot_apply_of_ne k hh,
      huv hx, huv (shift_mem_halfSpace k hk h hx)]

private theorem standardTest_indicator_eqOn {u η : E → ℝ}
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    EqOn (standardNirenbergTest k h η ((halfSpace d).indicator u))
      (standardNirenbergTest k h η u) (halfSpace d) := by
  have hi : EqOn ((halfSpace d).indicator u) u (halfSpace d) :=
    fun x hx => indicator_of_mem hx u
  have hd := diffQuot_eqOn_halfSpace hi k hk h
  apply diffQuot_eqOn_halfSpace (k := k) (hk := hk) (h := -h)
  intro x hx
  exact congrArg (fun a : ℝ => η x ^ 2 * a) (hd hx)

private theorem weakPartial_indicator {u : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d)))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d)) (i : Fin d) :
    HasWeakPartialDeriv i ((halfSpace d).indicator (p i)) ((halfSpace d).indicator u) univ := by
  let w : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u (halfSpace d) :=
    { memLp := by simpa using hu.1.1
      weakGrad := fun x => WithLp.toLp 2 (fun j => p j x)
      weakGrad_component_memLp := fun j => by simpa using hp j
      isWeakGrad := hw }
  have hu' : MemW01p (ENNReal.ofReal (2 : ℝ)) u (halfSpace d) := by simpa using hu
  exact (zeroExtendMemW1pWitnessP isOpen_halfSpace (by norm_num : (1 : ℝ) < 2) hu' w).isWeakGrad i


theorem tangential_nirenberg_identity
    {u f : E → ℝ} {p F : Fin d → E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d)))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (halfSpace d)))
    (hf : MemLp f 2 (volume.restrict (halfSpace d)))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ halfSpace d →
      (∫ x in halfSpace d, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in halfSpace d, f x * φ x)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (k : Fin d) (hk : k ≠ 0) {h : ℝ} (hh : h ≠ 0) :
    -(∑ i, ∫ x,
      diffQuot k h ((halfSpace d).indicator (F i)) x *
        nirenbergTestPartial k i h η ((halfSpace d).indicator u)
          (fun j => (halfSpace d).indicator (p j)) x) =
      ∫ x in halfSpace d, f x * standardNirenbergTest k h η u x := by
  let u₀ := (halfSpace d).indicator u
  let p₀ : Fin d → E → ℝ := fun i => (halfSpace d).indicator (p i)
  let F₀ : Fin d → E → ℝ := fun i => (halfSpace d).indicator (F i)
  let r : Fin d → E → ℝ := fun i => nirenbergTestPartial k i h η u₀ p₀
  let q : Fin d → E → ℝ := fun i => diffQuot k (-h) (r i)
  let v := standardNirenbergTest k h η u
  let v₀ := standardNirenbergTest k h η u₀
  have hu₀ : MemLp u₀ 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu.1.1
  have hp₀ (i : Fin d) : MemLp (p₀ i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hp i)
  have hF₀ (i : Fin d) : MemLp (F₀ i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hF i)
  have hw₀ (i : Fin d) : HasWeakPartialDeriv i (p₀ i) u₀ univ :=
    weakPartial_indicator hu hp hw i
  have hr (i : Fin d) : MemLp (r i) 2 volume :=
    nirenbergTestPartial_memLp hu₀ hp₀ hη hc k i h
  have hq (i : Fin d) : MemLp (q i) 2 volume := memLp_diffQuot_two k (-h) (hr i)
  have hv : MemW01p 2 v (halfSpace d) := memW01p_standardNirenbergTest hu hη hc k hk h
  have hvEq : EqOn v₀ v (halfSpace d) := standardTest_indicator_eqOn k hk h
  have hwq (i : Fin d) : HasWeakPartialDeriv i (q i) v (halfSpace d) := by
    have hg : HasWeakPartialDeriv i (q i) v₀ univ :=
      hasWeakPartialDeriv_standardNirenbergTest k i h hη
        (by simpa using hu₀.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        (by simpa using (hp₀ i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) (hw₀ i)
    intro φ hφ hφc hφs
    calc
      _ = ∫ x in halfSpace d, v₀ x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
        rw [hvEq hx]
      _ = _ := (hg.restrict isOpen_halfSpace (subset_univ _)) φ hφ hφc hφs
  have htest := weakEquation_of_memW01p isOpen_halfSpace hF hf heq hv
    (fun i => (hq i).restrict _) hwq
  have hwhole : (∫ x in halfSpace d, ∑ i, F i x * q i x) =
      ∫ x, ∑ i, F₀ i x * q i x := by
    rw [← integral_indicator isOpen_halfSpace.measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ halfSpace d <;> simp [F₀, hx]
  rw [hwhole] at htest
  have hsum : (∫ x, ∑ i, F₀ i x * q i x) = ∑ i, ∫ x, F₀ i x * q i x := by
    simpa using integral_finsetSum Finset.univ (fun i _ => (hF₀ i).integrable_mul (hq i))
  rw [hsum] at htest
  have hibp (i : Fin d) : (∫ x, F₀ i x * q i x) =
      -(∫ x, diffQuot k h (F₀ i) x * r i x) := by
    have hi := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh (hF₀ i) (hr i)
    dsimp [q]
    linarith
  simpa only [hibp, Finset.sum_neg_distrib] using htest

end Poincare.Analysis.Sobolev.BoundaryTangential
