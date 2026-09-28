import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.LocalIdentity
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Substitution.Assembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak NirenbergStandardTest NirenbergEuclidean NirenbergAssembly
open NirenbergCrossBoundsNonSmooth NirenbergSubstitutionNonSmooth
open Poincare.Analysis.Elliptic

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem diffQuot_indicator_tangential (u : E → ℝ)
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    diffQuot k h ((halfSpace d).indicator u) =
      (halfSpace d).indicator (diffQuot k h u) := by
  funext x
  by_cases hh : h = 0
  · simp [hh]
  have hs : x + h • EuclideanSpace.single k 1 ∈ halfSpace d ↔ x ∈ halfSpace d := by
    simp [halfSpace, PiLp.add_apply, PiLp.smul_apply, hk.symm]
  by_cases hx : x ∈ halfSpace d <;>
    simp [diffQuot_apply_of_ne k hh, hs, hx]

private theorem standardTest_indicator_tangential (u η : E → ℝ)
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    standardNirenbergTest k h η ((halfSpace d).indicator u) =
      (halfSpace d).indicator (standardNirenbergTest k h η u) := by
  unfold standardNirenbergTest
  have hm : (fun x => η x ^ 2 * diffQuot k h ((halfSpace d).indicator u) x) =
      (halfSpace d).indicator (fun x => η x ^ 2 * diffQuot k h u x) := by
    rw [diffQuot_indicator_tangential u k hk h]
    funext x
    by_cases hx : x ∈ halfSpace d <;> simp [hx]
  rw [hm, diffQuot_indicator_tangential _ k hk (-h)]

private theorem setIntegral_indicator_sq (V : Set E) (u : E → ℝ) :
    (∫ x in V, ((halfSpace d).indicator u x) ^ 2) =
      ∫ x in V ∩ halfSpace d, (u x) ^ 2 := by
  rw [← setIntegral_indicator isOpen_halfSpace.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ halfSpace d <;> simp [hx]

private theorem setIntegral_sum_indicator_sq (V : Set E) (p : Fin d → E → ℝ) :
    (∫ x in V, ∑ i : Fin d, ((halfSpace d).indicator (p i) x) ^ 2) =
      ∫ x in V ∩ halfSpace d, ∑ i : Fin d, (p i x) ^ 2 := by
  rw [← setIntegral_indicator isOpen_halfSpace.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ halfSpace d <;> simp [hx]

private theorem extended_weakPartial {u : E → ℝ} {p : Fin d → E → ℝ}
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

private theorem energy_le_of_identity {L P C1 C2 C3 R Q : ℝ}
    (hcoer : L ≤ P) (hid : -(P + C1 + C2 + C3) = R) :
    L ≤ |C1| + |C2| + |C3| + |R| + |Q| := by
  linarith [neg_le_abs C1, neg_le_abs C2, neg_le_abs C3, neg_le_abs R, abs_nonneg Q]

theorem local_tangential_diffQuot_weakGradient_localL2_bound
    {O W : Set E} (B : SmoothEllipticBilinearForm d O)
    (hW : IsOpen W) {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hf : MemLp f 2 (volume.restrict (W ∩ halfSpace d)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d)))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d))
    (hF : ∀ j, MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x)
      2 (volume.restrict (W ∩ halfSpace d)))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ j : Fin d,
        (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηrange : range η ⊆ Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (hDη : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {O' O'' : Set E} (hO' : IsOpen O') (hO'O : closure O' ⊆ O)
    (hO'c : IsCompact (closure O')) (hO'W : O' ⊆ W)
    {R : ℝ} (hR : 0 < R)
    (hthick : ∀ {h : ℝ}, |h| ≤ R → Metric.cthickening |h| (tsupport η) ⊆ O')
    (hηone : ∀ x ∈ O'', η x = 1) (hO'' : MeasurableSet O'')
    (k : Fin d) (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R →
      (B.lam / 2) * (∫ x in O'' ∩ halfSpace d,
        ∑ i : Fin d, (diffQuot k h (p i) x) ^ 2) ≤
      C * ((∫ x in O' ∩ halfSpace d, ∑ i : Fin d, (p i x) ^ 2) +
        (∫ x in O' ∩ halfSpace d, (u x) ^ 2) +
        (∫ x in O' ∩ halfSpace d, (f x) ^ 2)) := by
  classical
  let u₀ := (halfSpace d).indicator u
  let f₀ := (W ∩ halfSpace d).indicator f
  let p₀ : Fin d → E → ℝ := fun i => (halfSpace d).indicator (p i)
  have hu₀ : MemLp u₀ 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu.1.1
  have hWH : IsOpen (W ∩ halfSpace d) := hW.inter isOpen_halfSpace
  have hf₀ : MemLp f₀ 2 volume :=
    (memLp_indicator_iff_restrict hWH.measurableSet).mpr hf
  have hp₀ (i : Fin d) : MemLp (p₀ i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hp i)
  have hw₀ (i : Fin d) : HasWeakPartialDeriv i (p₀ i) u₀ univ :=
    extended_weakPartial hu hp hw i
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R →
      (B.lam / 2) * (∫ x in O'', ∑ i : Fin d, (diffQuot k h (p₀ i) x) ^ 2) ≤
      C * ((∫ x in O', ∑ i : Fin d, (p₀ i x) ^ 2) +
        (∫ x in O', (u₀ x) ^ 2) + (∫ x in O', (f₀ x) ^ 2)) := by
    refine nirenberg_diffQuot_g_localL2_bound B hu₀ (fun {_} _ => hf₀.restrict _) hp₀
      hη hηc hηrange hN hDη hO' hO'O hO'c hthick hηone hO'' k ?_ ?_ ?_
    · intro h hh hh_le
      have hthick' : Metric.cthickening R (closure (tsupport η)) ⊆ O' := by
        simpa only [(isClosed_tsupport η).closure_eq, abs_of_pos hR] using
          hthick (h := R) (by rw [abs_of_pos hR])
      have hFK := integral_sq_diffQuot_le_integral_sq_weakPartial_meas hu₀ (hp₀ k) k
        (hw₀ k) hO'.measurableSet (isClosed_tsupport η).measurableSet
        (by simpa only [(isClosed_tsupport η).closure_eq] using hηc.isCompact)
        hR hthick' hh hh_le
      refine hFK.trans (integral_mono ?_ ?_ ?_)
      · exact ((hp₀ k).integrable_sq).restrict
      · exact integrable_finsetSum _ (fun i _ => (hp₀ i).integrable_sq.restrict)
      · intro x
        exact Finset.single_le_sum (fun i _ => sq_nonneg (p₀ i x)) (Finset.mem_univ k)
    · intro h hh _
      exact nirenbergTestFunction_sq_integral_le_weak hu₀ (hp₀ k) k (hw₀ k)
        hη hηc hηrange hDη hh
    · intro h hh hh_le
      have hcoer := principal_term_ge_lambda_norm_sq_nonsmooth B hp₀ hη hηc hO'O hthick k hh_le
      have hflux (j : Fin d) :
          (halfSpace d).indicator (fun x => ∑ i : Fin d, B.a x i j * p i x) =
          fun x => ∑ i : Fin d, B.a x i j * p₀ i x := by
        funext x
        by_cases hx : x ∈ halfSpace d <;> simp [p₀, hx]
      have htestO : tsupport (standardNirenbergTest k h η u₀) ⊆ O :=
        (NirenbergTestFunction.tsupport_nirenbergTestFunction_subset η u₀ k h).trans
          ((hthick hh_le).trans (subset_closure.trans hO'O))
      have hRhs : (∫ x in W ∩ halfSpace d, f x * standardNirenbergTest k h η u x) =
          ∫ x in O, f₀ x * NirenbergTestFunction.nirenbergTestFunction k h η u₀ x := by
        have hm : (W ∩ halfSpace d).indicator (fun x => f x * standardNirenbergTest k h η u x) =
            fun x => f₀ x * standardNirenbergTest k h η u₀ x := by
          funext x
          dsimp [f₀, u₀]
          rw [standardTest_indicator_tangential u η k hk h]
          by_cases hxW : x ∈ W <;> by_cases hxH : x ∈ halfSpace d <;> simp [hxW, hxH]
        rw [← integral_indicator hWH.measurableSet, hm]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (htestO hmem)), mul_zero])).symm
      have hid := local_tangential_nirenberg_identity hW hu hp hw hF hf heq hη hηc k hk hh
        ((hthick hh_le).trans hO'W)
      simp only [hflux, nirenbergTestPartial] at hid
      rw [flux_pairing_expansion B hu₀ hp₀ hη hηc k hh, hRhs] at hid
      exact energy_le_of_identity hcoer hid
  have hfdata : (∫ x in O', f₀ x ^ 2) = ∫ x in O' ∩ halfSpace d, f x ^ 2 := by
    calc
      _ = ∫ x in O', ((halfSpace d).indicator f x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hO'.measurableSet] with x hx
        by_cases hxH : x ∈ halfSpace d <;> simp [f₀, hO'W hx, hxH]
      _ = _ := setIntegral_indicator_sq O' f
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨C, hC, fun {h} hh hh_le => ?_⟩
  have hb := hbound hh hh_le
  rw [hfdata] at hb
  dsimp [u₀, p₀] at hb
  simp_rw [diffQuot_indicator_tangential _ k hk h,
    setIntegral_sum_indicator_sq, setIntegral_indicator_sq] at hb
  exact hb

end Poincare.Analysis.Sobolev.BoundaryTangential
