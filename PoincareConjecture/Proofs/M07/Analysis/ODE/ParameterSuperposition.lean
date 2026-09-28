import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterCurveSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic









open Filter Set
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Poincare.ODE.Parameter

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

section GeneralTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in

def superpositionGen (f : E → F) : C(K, E) → C(K, F) := fun α =>
  if h : Continuous (f ∘ α) then ⟨f ∘ α, h⟩ else 0

lemma superpositionGen_apply_of_continuousOn {f : E → F} {s : Set E}
    (hf : ContinuousOn f s) (α : C(K, E)) (hα : ∀ t, α t ∈ s) (t : K) :
    superpositionGen f α t = f (α t) := by
  have h : Continuous (f ∘ α) := hf.comp_continuous α.continuous hα
  simp only [superpositionGen]
  rw [dif_pos h]
  rfl

lemma superpositionGen_apply {f : E → F} (hf : Continuous f) (α : C(K, E)) (t : K) :
    superpositionGen f α t = f (α t) :=
  superpositionGen_apply_of_continuousOn hf.continuousOn α (fun _ => Set.mem_univ _) t

lemma superpositionGen_eq_superposition (f : E → E) :
    superpositionGen (K := K) f = superposition f := rfl

theorem continuous_superpositionGen {f : E → F} (hf : Continuous f) :
    Continuous (superpositionGen (K := K) f) := by
  rw [Metric.continuous_iff]
  intro α₀ ε hε
  have hcomp : IsCompact (Set.range α₀) := isCompact_range α₀.continuous
  obtain ⟨δ, hδ, H⟩ :=
    hcomp.exists_forall_dist_image_lt_of_continuousAt (fun x _ => hf.continuousAt) hε
  refine ⟨δ, hδ, fun α hα => ?_⟩
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  rw [superpositionGen_apply hf, superpositionGen_apply hf, dist_comm]
  refine H (α₀ t) (Set.mem_range_self t) (α t) ?_
  calc dist (α₀ t) (α t) ≤ dist α₀ α := ContinuousMap.dist_apply_le_dist t
    _ = dist α α₀ := dist_comm _ _
    _ < δ := hα

theorem hasStrictFDerivAt_superpositionGen
    {f : E → F} {f' : E → E →L[ℝ] F} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {α₀ : C(K, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(K, E →L[ℝ] F)} (hA₀ : ∀ t, A₀ t = f' (α₀ t)) :
    HasStrictFDerivAt (superpositionGen f) (postcompCurve A₀) α₀ := by
  have hcont : ContinuousOn f u := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hrange : IsCompact (Set.range α₀) := isCompact_range α₀.continuous
  have hrangeu : Set.range α₀ ⊆ u := Set.range_subset_iff.mpr hmem
  obtain ⟨δ₁, hδ₁, hthick⟩ := hrange.exists_thickening_subset_open hu hrangeu
  refine .of_isLittleO (Asymptotics.isLittleO_iff.mpr fun ε hε => ?_)
  have hcrange : ∀ x ∈ Set.range α₀, ContinuousAt f' x := by
    rintro x ⟨t, rfl⟩; exact hc t
  obtain ⟨δ₂, hδ₂, hunif⟩ :=
    hrange.exists_forall_dist_image_lt_of_continuousAt hcrange (half_pos hε)
  have hδpos : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hball : ∀ t, Metric.ball (α₀ t) (min δ₁ δ₂) ⊆ u := fun t y hy =>
    hthick (Metric.mem_thickening_iff.mpr ⟨α₀ t, Set.mem_range_self t,
      (Metric.mem_ball.mp hy).trans_le (min_le_left _ _)⟩)
  have key : ∀ t : K, ∀ a ∈ Metric.ball (α₀ t) (min δ₁ δ₂),
      ∀ b ∈ Metric.ball (α₀ t) (min δ₁ δ₂),
      ‖f a - f b - f' (α₀ t) (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro t a ha b hb
    have hg : ∀ y ∈ Metric.ball (α₀ t) (min δ₁ δ₂),
        HasFDerivWithinAt (fun z => f z - f' (α₀ t) z) (f' y - f' (α₀ t))
          (Metric.ball (α₀ t) (min δ₁ δ₂)) y := fun y hy =>
      ((hd y (hball t hy)).sub (f' (α₀ t)).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ y ∈ Metric.ball (α₀ t) (min δ₁ δ₂), ‖f' y - f' (α₀ t)‖ ≤ ε :=
      fun y hy => by
        have h1 : dist (α₀ t) y < δ₂ := by
          rw [dist_comm]
          exact (Metric.mem_ball.mp hy).trans_le (min_le_right _ _)
        have h2 := hunif (α₀ t) (Set.mem_range_self t) y h1
        rw [dist_eq_norm] at h2
        calc ‖f' y - f' (α₀ t)‖ = ‖f' (α₀ t) - f' y‖ := norm_sub_rev _ _
          _ ≤ ε := by linarith
    have hmvt := (convex_ball (α₀ t) (min δ₁ δ₂)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hg hbound hb ha
    calc ‖f a - f b - f' (α₀ t) (a - b)‖
        = ‖(f a - f' (α₀ t) a) - (f b - f' (α₀ t) b)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ε * ‖a - b‖ := hmvt
  filter_upwards [prod_mem_nhds
    (Metric.ball_mem_nhds α₀ hδpos) (Metric.ball_mem_nhds α₀ hδpos)]
  rintro ⟨α, β⟩ ⟨hα, hβ⟩
  have hval : ∀ {γ : C(K, E)}, γ ∈ Metric.ball α₀ (min δ₁ δ₂) →
      ∀ t, γ t ∈ Metric.ball (α₀ t) (min δ₁ δ₂) := by
    intro γ hγ t
    rw [Metric.mem_ball, dist_eq_norm] at hγ ⊢
    calc ‖γ t - α₀ t‖ = ‖(γ - α₀) t‖ := by rw [ContinuousMap.sub_apply]
      _ ≤ ‖γ - α₀‖ := ContinuousMap.norm_coe_le_norm _ t
      _ < min δ₁ δ₂ := hγ
  have hαval : ∀ t, α t ∈ u := fun t => hball t (hval hα t)
  have hβval : ∀ t, β t ∈ u := fun t => hball t (hval hβ t)
  refine (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr fun t => ?_
  have hpt : (superpositionGen f α - superpositionGen f β - postcompCurve A₀ (α - β)) t
      = f (α t) - f (β t) - f' (α₀ t) (α t - β t) := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, postcompCurve_apply,
      ContinuousMap.sub_apply, hA₀,
      superpositionGen_apply_of_continuousOn hcont α hαval,
      superpositionGen_apply_of_continuousOn hcont β hβval]
  rw [hpt]
  have h2 : ‖α t - β t‖ ≤ ‖α - β‖ := by
    have h3 := ContinuousMap.norm_coe_le_norm (α - β) t
    rwa [ContinuousMap.sub_apply] at h3
  exact (key t _ (hval hα t) _ (hval hβ t)).trans (mul_le_mul_of_nonneg_left h2 hε.le)

end GeneralTarget

section PostcompL

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def postcompCurveLM : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) where
  toFun A := postcompCurve A
  map_add' A B := by
    ext β t
    simp only [postcompCurve_apply, add_apply, ContinuousMap.add_apply]
  map_smul' c A := by
    ext β t
    simp only [postcompCurve_apply, smul_apply, ContinuousMap.smul_apply,
      RingHom.id_apply]

@[simp] lemma postcompCurveLM_apply (A : C(K, E →L[ℝ] F)) :
    postcompCurveLM A = postcompCurve A := rfl

def postcompCurveL : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  postcompCurveLM.mkContinuous 1
    (fun (A : C(K, E →L[ℝ] F)) => by rw [one_mul]; exact norm_postcompCurve_le A)

@[simp] lemma postcompCurveL_apply (A : C(K, E →L[ℝ] F)) :
    postcompCurveL A = postcompCurve A := by
  simp only [postcompCurveL, LinearMap.mkContinuous_apply, postcompCurveLM_apply]

end PostcompL

theorem contDiff_superpositionGen_nat (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      ContDiff ℝ (n : WithTop ℕ∞) f → ContDiff ℝ (n : WithTop ℕ∞) (superpositionGen (K := K) f) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    rw [Nat.cast_zero, contDiff_zero] at hf ⊢
    exact continuous_superpositionGen hf
  | succ k ih =>
    intro F _ _ f hf
    rw [Nat.cast_succ] at hf ⊢
    obtain ⟨hf_diff, -, hf_fderiv⟩ := contDiff_succ_iff_fderiv.mp hf
    have hf_cont_fderiv : Continuous (fderiv ℝ f) :=
      hf.continuous_fderiv (by exact_mod_cast Nat.succ_ne_zero k)
    have hHas : ∀ α : C(K, E),
        HasStrictFDerivAt (superpositionGen f)
          (postcompCurve (superpositionGen (fderiv ℝ f) α)) α := by
      intro α
      refine hasStrictFDerivAt_superpositionGen (f' := fderiv ℝ f) (u := Set.univ) isOpen_univ
        (fun x _ => hf_diff.differentiableAt.hasFDerivAt) (fun _ => Set.mem_univ _)
        (fun _ => hf_cont_fderiv.continuousAt) ?_
      intro t
      exact superpositionGen_apply hf_cont_fderiv α t
    have hfderiv_eq : fderiv ℝ (superpositionGen f)
        = fun (α : C(K, E)) => postcompCurveL (superpositionGen (fderiv ℝ f) α) := by
      funext α
      rw [(hHas α).hasFDerivAt.fderiv, postcompCurveL_apply]
    rw [contDiff_succ_iff_fderiv]
    refine ⟨fun α => (hHas α).hasFDerivAt.differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [hfderiv_eq]
    exact ContDiff.continuousLinearMap_comp postcompCurveL (ih hf_fderiv)

theorem contDiff_superpositionGen_infty {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superpositionGen (K := K) f) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_superpositionGen_nat n (contDiff_infty.mp hf n)

theorem contDiff_superposition_infty {f : E → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superposition (K := K) f) := by
  rw [← superpositionGen_eq_superposition]
  exact contDiff_superpositionGen_infty hf

end Poincare.ODE.Parameter

end
