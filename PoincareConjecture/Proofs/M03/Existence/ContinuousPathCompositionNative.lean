import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

open Set Metric Filter
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.ContinuousPathCompositionNative

universe u v

variable (K : Type v) [TopologicalSpace K] [CompactSpace K]
  {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pointwiseOperator (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟨fun s => A s (h s), A.continuous.clm_apply h.continuous⟩
      map_add' := by intros; ext s; simp
      map_smul' := by intros; ext s; simp }
    ‖A‖ (fun h => (ContinuousMap.norm_le _ (by positivity)).mpr fun s => by
      exact (A s).le_opNorm (h s) |>.trans
        (mul_le_mul (A.norm_coe_le_norm s) (h.norm_coe_le_norm s)
          (norm_nonneg (h s)) (norm_nonneg A)))

@[simp] theorem pointwiseOperator_apply (A : C(K, E →L[ℝ] F))
    (h : C(K, E)) (s : K) : pointwiseOperator K A h s = A s (h s) := rfl

theorem norm_pointwiseOperator_le (A : C(K, E →L[ℝ] F)) :
    ‖pointwiseOperator K A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro h
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro s
  exact (A s).le_opNorm (h s) |>.trans
    (mul_le_mul (A.norm_coe_le_norm s) (h.norm_coe_le_norm s)
      (norm_nonneg (h s)) (norm_nonneg A))

def pointwiseOperatorCLM :
    C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := pointwiseOperator K
      map_add' := by intros; ext h s; simp
      map_smul' := by intros; ext h s; simp }
    1 (fun A => by simpa using norm_pointwiseOperator_le K A)

@[simp] theorem pointwiseOperatorCLM_apply (A : C(K, E →L[ℝ] F)) :
    pointwiseOperatorCLM K A = pointwiseOperator K A := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_postcomp (f : C(E, F)) (f' : C(E, E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt f (f' x) x) (u : C(K, E)) :
    HasFDerivAt (fun v : C(K, E) => f.comp v)
      (pointwiseOperator K (f'.comp u)) u := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff
    (f := fun v : C(K, E) => f'.comp v) (a := u)).mp
      (f'.continuous_postcomp (X := K)).continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds u hδ] with v hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro s
  have heval : ‖(ContinuousMap.evalCLM ℝ s : C(K, E) →L[ℝ] E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro h
    simpa using h.norm_coe_le_norm s
  have hbound : ∀ z ∈ ball u δ,
      ‖(f' (z s)).comp (ContinuousMap.evalCLM ℝ s) -
        (f' (u s)).comp (ContinuousMap.evalCLM ℝ s)‖ ≤ ε := by
    intro z hz
    have hfield : ‖f' (z s) - f' (u s)‖ ≤ ε := by
      have h := (f'.comp z - f'.comp u).norm_coe_le_norm s
      have hnorm : ‖f'.comp z - f'.comp u‖ < ε := by
        have hdist := hclose (mem_ball.mp hz)
        rw [dist_eq_norm (f'.comp z) (f'.comp u)] at hdist
        exact hdist
      exact h.trans hnorm.le
    calc
      ‖(f' (z s)).comp (ContinuousMap.evalCLM ℝ s) -
          (f' (u s)).comp (ContinuousMap.evalCLM ℝ s)‖ =
          ‖(f' (z s) - f' (u s)).comp (ContinuousMap.evalCLM ℝ s)‖ := rfl
      _ ≤ ‖f' (z s) - f' (u s)‖ *
          ‖(ContinuousMap.evalCLM ℝ s : C(K, E) →L[ℝ] E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ε * 1 := mul_le_mul hfield heval (norm_nonneg _) hε.le
      _ = ε := mul_one ε
  have hrem := (convex_ball u δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun z : C(K, E) => f (z s))
    (f' := fun z => (f' (z s)).comp (ContinuousMap.evalCLM ℝ s))
    (φ := (f' (u s)).comp (ContinuousMap.evalCLM ℝ s))
    (fun z _ => by
      have h := (hf (z s)).comp z
        ((ContinuousMap.evalCLM ℝ s : C(K, E) →L[ℝ] E).hasFDerivAt (x := z))
      simpa only [Function.comp_def, ContinuousMap.evalCLM_apply] using
        h.hasFDerivWithinAt (s := ball u δ))
    hbound (mem_ball_self hδ) hv
  simpa only [ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    pointwiseOperator_apply, ContinuousLinearMap.comp_apply,
    ContinuousMap.evalCLM_apply] using hrem

theorem contDiff_postcomp_nat (k : ℕ) (f : C(E, F))
    (hf : ContDiff ℝ k (f : E → F)) :
    ContDiff ℝ k (fun u : C(K, E) => f.comp u) := by
  induction k generalizing F with
  | zero => exact contDiff_zero.mpr (f.continuous_postcomp (X := K))
  | succ k ih =>
    obtain ⟨f', hf', hder⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let A : C(E, E →L[ℝ] F) := ⟨f', hf'.continuous⟩
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => pointwiseOperator K (A.comp u), ?_, ?_⟩
    · exact (pointwiseOperatorCLM K).contDiff.comp (ih A hf')
    · intro u
      exact hasFDerivAt_postcomp K f A hder u

theorem contDiff_postcomp_of_order {k : ℕ∞} (f : C(E, F))
    (hf : ContDiff ℝ k (f : E → F)) :
    ContDiff ℝ k (fun u : C(K, E) => f.comp u) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro m hm
  exact contDiff_postcomp_nat K m f ((contDiff_iff_forall_nat_le.mp hf) m hm)

theorem contDiff_postcomp (f : C(E, F)) (hf : ContDiff ℝ ∞ (f : E → F)) :
    ContDiff ℝ ∞ (fun u : C(K, E) => f.comp u) :=
  contDiff_postcomp_of_order K f hf

end PoincareConjecture.ContinuousPathCompositionNative

end
