import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.LocalEstimate
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak NirenbergEuclidean NirenbergCrossBoundsNonSmooth

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem diffQuot_indicator_eq_of_mem (v : E → ℝ)
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) {x : E} (hx : x ∈ halfSpace d) :
    diffQuot k h ((halfSpace d).indicator v) x = diffQuot k h v x := by
  by_cases hh : h = 0
  · simp [hh]
  have hs : x + h • EuclideanSpace.single k 1 ∈ halfSpace d := by
    simpa [halfSpace, PiLp.add_apply, PiLp.smul_apply, hk.symm] using hx
  simp [diffQuot_apply_of_ne k hh, hx, hs]

theorem exists_tangential_weakPartial_of_local_weakEquation
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : E → ℝ} {p : Fin d → E → ℝ}
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
        ∫ x in W ∩ halfSpace d, f x * φ x) :
    ∀ k : Fin d, k ≠ 0 → ∀ i : Fin d, ∃ q : E → ℝ,
      MemLp q 2 (volume.restrict (V ∩ halfSpace d)) ∧
      HasWeakPartialDeriv k q (p i) (V ∩ halfSpace d) := by
  classical
  obtain ⟨U₀, hU₀, hVU₀, hU₀c⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  obtain ⟨U, hU, hVU, hUW₀⟩ := hVc.exists_isOpen_closure_subset
    ((hW.inter hU₀).mem_nhdsSet.mpr (subset_inter hVW hVU₀))
  have hUU₀ : closure U ⊆ U₀ := fun x hx => (hUW₀ hx).2
  have hUc : IsCompact (closure U) :=
    hU₀c.of_isClosed_subset isClosed_closure (hUU₀.trans subset_closure)
  have hUW : U ⊆ W := fun x hx => (hUW₀ (subset_closure hx)).1
  obtain ⟨η, hη, hηc, hηrange, hηone, hηU, N, hN, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hVc hU hVU
  obtain ⟨R, hR, hRU⟩ := hηc.isCompact.exists_cthickening_subset_open hU hηU
  have hVH : IsOpen (V ∩ halfSpace d) := hV.inter isOpen_halfSpace
  have hVHc : IsCompact (closure (V ∩ halfSpace d)) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  let p₀ : Fin d → E → ℝ := fun i => (halfSpace d).indicator (p i)
  have hp₀ (i : Fin d) : MemLp (p₀ i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hp i)
  intro k hk i
  obtain ⟨C, _, hC⟩ := local_tangential_diffQuot_weakGradient_localL2_bound B hW hu hf hp hw hF heq
    hη hηc hηrange hN hDη hU (subset_univ _) hUc hUW hR
    (fun {h} hh => (Metric.cthickening_mono hh _).trans hRU)
    (fun x hx => hηone x (subset_closure hx)) hV.measurableSet k hk
  let C₀ : ℝ := (C * ((∫ x in U ∩ halfSpace d, ∑ j : Fin d, p j x ^ 2) +
    (∫ x in U ∩ halfSpace d, u x ^ 2) +
    (∫ x in U ∩ halfSpace d, f x ^ 2))) / (B.lam / 2)
  have hbound (h : ℝ) (hh : 0 < |h|) (hle : |h| ≤ R) :
      eLpNorm (diffQuot k h (p₀ i)) 2 (volume.restrict (V ∩ halfSpace d)) ≤
        ENNReal.ofReal (Real.sqrt C₀) := by
    have hq (j : Fin d) := (memLp_diffQuot_two k h (hp₀ j)).restrict (V ∩ halfSpace d)
    have hsq (j : Fin d) : Integrable (fun x => diffQuot k h (p₀ j) x ^ 2)
        (volume.restrict (V ∩ halfSpace d)) := (hq j).integrable_sq
    apply eLpNorm_two_le_sqrt_of_integral_sq_le (hq i)
    calc
      _ ≤ ∫ x in V ∩ halfSpace d, ∑ j : Fin d, diffQuot k h (p₀ j) x ^ 2 := by
        apply integral_mono (hsq i) (integrable_finsetSum _ (fun j _ => hsq j))
        intro x
        exact Finset.single_le_sum (fun j _ => sq_nonneg (diffQuot k h (p₀ j) x))
          (Finset.mem_univ i)
      _ = ∫ x in V ∩ halfSpace d, ∑ j : Fin d, diffQuot k h (p j) x ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
        apply Finset.sum_congr rfl
        intro j _
        rw [show diffQuot k h (p₀ j) x = diffQuot k h (p j) x from
          diffQuot_indicator_eq_of_mem (p j) k hk h hx.2]
      _ ≤ C₀ := (le_div_iff₀ (div_pos B.hlam_pos (by norm_num))).mpr (by
        simpa only [mul_comm] using hC (abs_pos.mp hh) hle)
  obtain ⟨q, hq, hweak, _⟩ := hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
    isOpen_univ hVH hVHc hR (subset_univ _) (by simpa using hp₀ i)
    k (Real.sqrt_nonneg C₀) hbound
  refine ⟨q, hq, ?_⟩
  intro φ hφ hφc hφs
  calc
    _ = ∫ x in V ∩ halfSpace d, p₀ i x * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
      simp [p₀, hx.2]
    _ = _ := hweak φ hφ hφc hφs

end Poincare.Analysis.Sobolev.BoundaryTangential
