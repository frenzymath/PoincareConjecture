import PoincareConjecture.Proofs.M36.RadialWeights
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean
import Mathlib.Analysis.Calculus.ContDiff.Bounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M36

section Families

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem parametric_iteratedFDeriv_contDiff {f : ℝ → E → F}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => iteratedFDeriv ℝ k (f p.1) p.2) := by
  induction k with
  | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ E F).symm :
          F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F)
  | succ k ih =>
      have hpartial : ContDiff ℝ ∞
          (fun p : ℝ × E => fderiv ℝ (iteratedFDeriv ℝ k (f p.1)) p.2) :=
        (ih.comp ((contDiff_fst.fst).prodMk contDiff_snd)).fderiv
          contDiff_snd (by simp)
      exact hpartial.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm :
          (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F)

theorem parametric_jets_eventually_small {f : ℝ → E → F}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {t₀ : ℝ}
    (hzero : f t₀ = fun _ => 0) {K : Set E} (hK : IsCompact K)
    (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ t in nhds t₀, ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (f t) x‖ < eta := by
  have hj (i : Fin (m + 1)) : ∀ᶠ t in nhds t₀, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ (i : ℕ) (f t) x‖ < eta := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have hcont := ((parametric_iteratedFDeriv_contDiff hf (i : ℕ)).continuous.continuousAt
      (x := (t₀, x))).norm
    have hbase : ‖iteratedFDeriv ℝ (i : ℕ) (f t₀) x‖ < eta := by
      simpa [hzero] using heta
    exact hcont.eventually (gt_mem_nhds hbase)
  filter_upwards [Filter.eventually_all.mpr hj] with t ht k hk x hx
  exact ht ⟨k, Nat.lt_succ_of_le hk⟩ x hx

theorem exists_parametric_jet_bound {f : ℝ → E → F}
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    {T : Set ℝ} (hT : IsCompact T) {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t ∈ T, ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (f t) x‖ ≤ B := by
  classical
  choose C hC using fun i : Fin (m + 1) =>
    (hT.prod hK).exists_bound_of_continuousOn
      (parametric_iteratedFDeriv_contDiff hf (i : ℕ)).continuous.continuousOn
  let B := 1 + ∑ i : Fin (m + 1), max (C i) 0
  have hsum : 0 ≤ ∑ i : Fin (m + 1), max (C i) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨B, by dsimp [B]; linarith only [hsum], ?_⟩
  intro t ht k hk x hx
  let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  calc
    _ ≤ C i := hC i (t, x) ⟨ht, hx⟩
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j : Fin (m + 1), max (C j) 0 :=
      Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
    _ ≤ B := by dsimp [B]; linarith

end Families

theorem smoothProfile_joint_contDiff (C q : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothProfile C q p.1 p.2) :=
  (contDiff_const.mul contDiff_fst).mul
    (expNegInvGlue.contDiff.comp (contDiff_snd.div_const q))

theorem conformalFactor_joint_contDiff (C q : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => conformalFactor C q p.1 p.2) :=
  (contDiff_const.mul (smoothProfile_joint_contDiff C q)).exp

theorem radialConformalMultiplier_joint_contDiff (g₀ : StandardInitialMetric)
    (C q : ℝ) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞
      (fun p : ℝ × StandardCapSpace => radialConformalMultiplier g₀ C q p.1 r p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have htip : ContDiffAt ℝ ∞
      (fun z : ℝ × StandardCapSpace =>
        conformalFactor C q z.1 (g₀.cylindrical_end.radius + 4)) p :=
    (conformalFactor_joint_contDiff C q).contDiffAt.comp p
      (contDiffAt_fst.prodMk contDiffAt_const)
  by_cases hp : p.2 = 0
  · apply htip.congr_of_eventuallyEq
    have hzero : ∀ᶠ z in nhds p, radialTipWeight g₀ r z.2 = 0 := by
      have h := (continuous_snd.continuousAt (x := p)).tendsto.eventually
        (hp ▸ radialTipWeight_eventually_zero g₀ hr)
      exact h
    filter_upwards [hzero] with z hz
    simp [radialConformalMultiplier, hz]
  · have hweight := (radialTipWeight_contDiff g₀ hr).contDiffAt.comp p contDiffAt_snd
    have hheight := (standardSurgeryHeight_contDiffAt g₀ hp).comp p contDiffAt_snd
    exact (hweight.mul ((conformalFactor_joint_contDiff C q).contDiffAt.comp p
      (contDiffAt_fst.prodMk hheight))).add
      ((contDiffAt_const.sub hweight).mul htip)

theorem radialConformalMultiplier_zero (g₀ : StandardInitialMetric) (C q r : ℝ)
    (x : StandardCapSpace) : radialConformalMultiplier g₀ C q 0 r x = 1 := by
  simp [radialConformalMultiplier, conformalFactor, smoothProfile]

noncomputable def standardDilationError (g₀ : StandardInitialMetric) (a : ℝ)
    (x : StandardCapSpace) :=
  a ^ 2 • g₀.metric.euclideanCoefficients (a • x) - g₀.metric.euclideanCoefficients x

theorem standardDilationError_joint_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (Function.uncurry (standardDilationError g₀)) := by
  have hg : ContDiff ℝ ∞ g₀.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients
  exact ((contDiff_fst.pow 2).smul (hg.comp (contDiff_fst.smul contDiff_snd))).sub
    (hg.comp contDiff_snd)

theorem standardDilationError_one (g₀ : StandardInitialMetric) :
    standardDilationError g₀ 1 = fun _ => 0 := by
  funext x
  simp [standardDilationError]

theorem standardDilationError_jets_eventually_small (g₀ : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ a in nhds (1 : ℝ), ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (standardDilationError g₀ a) x‖ < eta :=
  parametric_jets_eventually_small (standardDilationError_joint_contDiff g₀)
    (standardDilationError_one g₀) hK m heta

noncomputable def standardScalarError (g₀ : StandardInitialMetric) (C q r epsilon : ℝ)
    (x : StandardCapSpace) :=
  (radialConformalMultiplier g₀ C q epsilon r x *
    (1 - 6 * epsilon * (1 - radialNeckWeight g₀ x)) - 1) •
      g₀.metric.euclideanCoefficients x

theorem standardScalarError_joint_contDiff (g₀ : StandardInitialMetric)
    (C q : ℝ) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (Function.uncurry (standardScalarError g₀ C q r)) := by
  have hg : ContDiff ℝ ∞ g₀.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients
  have ha := (radialNeckWeight_contDiff g₀).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × StandardCapSpace → StandardCapSpace))
  exact (((radialConformalMultiplier_joint_contDiff g₀ C q hr).mul
    (contDiff_const.sub ((contDiff_const.mul contDiff_fst).mul
      (contDiff_const.sub ha)))).sub contDiff_const).smul (hg.comp contDiff_snd)

theorem standardScalarError_zero (g₀ : StandardInitialMetric) (C q r : ℝ) :
    standardScalarError g₀ C q r 0 = fun _ => 0 := by
  funext x
  simp [standardScalarError, radialConformalMultiplier_zero]

theorem standardScalarError_jets_eventually_small (g₀ : StandardInitialMetric)
    (C q : ℝ) {r : ℝ} (hr : 0 < r) {K : Set StandardCapSpace} (hK : IsCompact K)
    (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ epsilon in nhds (0 : ℝ), ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (standardScalarError g₀ C q r epsilon) x‖ < eta :=
  parametric_jets_eventually_small (standardScalarError_joint_contDiff g₀ C q hr)
    (standardScalarError_zero g₀ C q r) hK m heta

end PoincareConjecture.M36
