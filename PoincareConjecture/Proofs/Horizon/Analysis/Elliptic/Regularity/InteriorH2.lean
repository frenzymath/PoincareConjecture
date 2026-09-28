import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.LocalEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.SecondDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Substitution.Assembly







noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.NirenbergAssembly

namespace Poincare.Analysis.Elliptic

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_memWkp_two_of_global_weakEquation
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    (hp : ∀ i, MemLp (p i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u univ)
    (hF : ∀ j, MemLp (fun x => ∑ i, B.a x i j * p i x) 2 volume)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ j, (∑ i, B.a x i j * p i x) *
        fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in V, f x * φ x)
    {x : E} (hx : x ∈ V) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ MemWkp 2 2 u W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV x hx
  have hr : 0 < ε / 2 := by positivity
  have hKV : closedBall x (ε / 2) ⊆ V :=
    (closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  obtain ⟨η, hη, hηc, hηrange, hηone, hηV, N, hN, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound
      (isCompact_closedBall x (ε / 2)) hV hKV
  obtain ⟨R, hR, hRV⟩ := hηc.isCompact.exists_cthickening_subset_open hV hηV
  have hWc : IsCompact (closure (ball x (ε / 2))) := by
    rw [closure_ball x hr.ne']
    exact isCompact_closedBall _ _
  refine ⟨ball x (ε / 2), isOpen_ball, mem_ball_self hr,
    ball_subset_closedBall.trans hKV, ?_⟩
  apply memWkp_two_of_integral_diffQuot_bound isOpen_ball hWc hu hp hw hR
  intro k
  obtain ⟨C, _, hC⟩ := diffQuot_weakGradient_localL2_bound B hV hu hf hp hw hF heq
    hη hηc hηrange hN hDη hV (subset_univ _) hVc (Subset.rfl) hR
    (fun {h} hh => (Metric.cthickening_mono hh _).trans hRV)
    (fun y hy => hηone y (ball_subset_closedBall hy)) measurableSet_ball k
  refine ⟨(C * ((∫ y in V, ∑ i, p i y ^ 2) +
    (∫ y in V, u y ^ 2) + (∫ y in V, f y ^ 2))) / (B.lam / 2), ?_⟩
  intro h hh hle
  exact (le_div_iff₀ (div_pos B.hlam_pos (by norm_num))).mpr (by
    simpa only [mul_comm] using hC hh hle)


theorem exists_memWkp_two_of_weakEquation
    {O : Set E} (hO : IsOpen O) (A : E → Matrix (Fin d) (Fin d) ℝ)
    (u f : E → ℝ) (p : Fin d → E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hf : ∀ K, IsCompact K → K ⊆ O → MemLp f 2 (volume.restrict K))
    (hpartial : ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * φ x))
    (heq : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x)
    {x : E} (hx : x ∈ O) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ MemWkp 2 2 u W := by
  obtain ⟨V, B, u₀, p₀, hV, hxV, hVc, hVO, _, huEq, _, _, _, hu₀, hp₀,
    hw₀, hF, hfV, heq₀⟩ :=
    exists_localized_weakEquation hO A u f p hA hpos hu hp hf hpartial heq hx
  let f₀ := V.indicator f
  have hf₀ : MemLp f₀ 2 volume :=
    (memLp_indicator_iff_restrict hV.measurableSet).mpr hfV
  have hF' (j : Fin d) : MemLp (fun y => ∑ i, B.a y i j * p₀ i y) 2 volume := by
    simpa only [B.symm] using hF j
  have heq' : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ y in V, ∑ j, (∑ i, B.a y i j * p₀ i y) *
        fderiv ℝ φ y (EuclideanSpace.single j 1)) = ∫ y in V, f₀ y * φ y := by
    intro φ hφ hφc hφV
    calc
      _ = ∫ y in V, f y * φ y := by
        simpa only [B.symm] using heq₀ φ hφ hφc hφV
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
        simp [f₀, hy]
  obtain ⟨W, hW, hxW, hWV, huW⟩ := exists_memWkp_two_of_global_weakEquation B
    hV hVc hu₀ hf₀ hp₀ hw₀ hF' heq' hxV
  refine ⟨W, hW, hxW, hWV.trans (subset_closure.trans hVO), ?_⟩
  apply (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW (u := u₀) (v := u) ?_).mp huW
  filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
  exact huEq (hWV hy)

end Poincare.Analysis.Elliptic
