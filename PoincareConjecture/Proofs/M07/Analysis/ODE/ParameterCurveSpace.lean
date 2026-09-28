import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology

namespace Poincare.ODE.Parameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ}

section CompactDomain

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def postcomp (A : E →L[ℝ] F) : C(K, E) →L[ℝ] C(K, F) :=
  A.compLeftContinuous ℝ K

omit [CompleteSpace E] [CompactSpace K] in
@[simp] lemma postcomp_apply (A : E →L[ℝ] F) (β : C(K, E)) (t : K) :
    postcomp A β t = A (β t) := rfl

omit [CompleteSpace E] in

lemma norm_postcomp_le (A : E →L[ℝ] F) :
    ‖(postcomp A : C(K, E) →L[ℝ] C(K, F))‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun β =>
    (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg β))).mpr fun t =>
      (A.le_opNorm (β t)).trans
        (mul_le_mul_of_nonneg_left (β.norm_coe_le_norm t) (norm_nonneg A))

def postcompCurve (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun β => ⟨fun t => A t (β t), A.continuous.clm_apply β.continuous⟩
      map_add' := fun β γ => by ext t; simp
      map_smul' := fun c β => by ext t; simp }
    ‖A‖
    (fun β => (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg β))).mpr
      fun t => ((A t).le_opNorm (β t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (β.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

omit [CompleteSpace E] in
@[simp] lemma postcompCurve_apply (A : C(K, E →L[ℝ] F)) (β : C(K, E)) (t : K) :
    postcompCurve A β t = A t (β t) := rfl

omit [CompleteSpace E] in

lemma norm_postcompCurve_le (A : C(K, E →L[ℝ] F)) :
    ‖(postcompCurve A : C(K, E) →L[ℝ] C(K, F))‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

omit [CompleteSpace E] in

lemma postcompCurve_const (A : E →L[ℝ] F) :
    postcompCurve (ContinuousMap.const K A) = (postcomp A : C(K, E) →L[ℝ] C(K, F)) := by
  refine ContinuousLinearMap.ext fun β => ?_
  ext t
  rfl

open Classical in

def superposition (f : E → E) : C(K, E) → C(K, E) := fun α =>
  if h : Continuous (f ∘ α) then ⟨f ∘ α, h⟩ else 0

omit [NormedSpace ℝ E] [CompleteSpace E] [CompactSpace K] in

lemma superposition_apply_of_continuousOn {f : E → E} {s : Set E}
    (hf : ContinuousOn f s) (α : C(K, E)) (hα : ∀ t, α t ∈ s) (t : K) :
    superposition f α t = f (α t) := by
  have h : Continuous (f ∘ α) := hf.comp_continuous α.continuous hα
  simp only [superposition]
  rw [dif_pos h]
  rfl

omit [NormedSpace ℝ E] [CompleteSpace E] [CompactSpace K] in

lemma superposition_const (f : E → E) (x : E) :
    superposition f (ContinuousMap.const K x) = ContinuousMap.const K (f x) := by
  have h : Continuous (f ∘ ⇑(ContinuousMap.const K x)) := by
    have h2 : f ∘ ⇑(ContinuousMap.const K x) = fun _ => f x := rfl
    rw [h2]; exact continuous_const
  ext t
  simp only [superposition]
  rw [dif_pos h]
  rfl

lemma _root_.IsCompact.exists_forall_dist_image_lt_of_continuousAt
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (hs : IsCompact s) {g : X → Y} (hg : ∀ x ∈ s, ContinuousAt g x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, dist x y < δ → dist (g x) (g y) < ε := by
  rcases Metric.mem_uniformity_dist.mp
      (hs.uniformContinuousAt_of_continuousAt g hg (Metric.dist_mem_uniformity hε)) with
    ⟨δ, hδ, H⟩
  exact ⟨δ, hδ, fun x hx y hxy => H hxy hx⟩

omit [CompleteSpace E] in

theorem hasStrictFDerivAt_superposition
    {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {α₀ : C(K, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(K, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t)) :
    HasStrictFDerivAt (superposition f) (postcompCurve A₀) α₀ := by
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
  have hpt : (superposition f α - superposition f β - postcompCurve A₀ (α - β)) t
      = f (α t) - f (β t) - f' (α₀ t) (α t - β t) := by
    simp [superposition_apply_of_continuousOn hcont α hαval,
      superposition_apply_of_continuousOn hcont β hβval, hA₀]
  rw [hpt]
  have h2 : ‖α t - β t‖ ≤ ‖α - β‖ := by
    have h3 := ContinuousMap.norm_coe_le_norm (α - β) t
    rwa [ContinuousMap.sub_apply] at h3
  exact (key t _ (hval hα t) _ (hval hβ t)).trans (mul_le_mul_of_nonneg_left h2 hε.le)

omit [CompleteSpace E] in

theorem hasStrictFDerivAt_superposition_const
    {f : E → E} {f' : E → E →L[ℝ] E} {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x ∈ Metric.ball x₀ ρ, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) :
    HasStrictFDerivAt (superposition f) (postcomp (f' x₀)) (ContinuousMap.const K x₀) := by
  rw [← postcompCurve_const (K := K) (f' x₀)]
  exact hasStrictFDerivAt_superposition Metric.isOpen_ball hd
    (fun _ => Metric.mem_ball_self hρ) (fun _ => hc) (fun _ => rfl)

end CompactDomain

def intervalPrimitive (hT : (0:ℝ) ≤ T) :
    C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
  LinearMap.mkContinuous
    { toFun := fun β =>
        ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT s),
          (intervalIntegral.continuous_primitive
            (fun a b => (β.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp
            continuous_subtype_val⟩
      map_add' := fun β γ => by
        ext t
        have hβ : IntervalIntegrable (fun s => β (Set.projIcc 0 T hT s))
            volume 0 (t : ℝ) := (β.continuous.comp continuous_projIcc).intervalIntegrable _ _
        have hγ : IntervalIntegrable (fun s => γ (Set.projIcc 0 T hT s))
            volume 0 (t : ℝ) := (γ.continuous.comp continuous_projIcc).intervalIntegrable _ _
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [intervalIntegral.integral_add hβ hγ]
      map_smul' := fun c β => by
        ext t
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply]
        rw [intervalIntegral.integral_smul] }
    T
    (fun β => (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg β))).mpr fun t => by
      calc ‖∫ s in (0:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT s)‖
          ≤ ‖β‖ * |(t:ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
            fun s _ => β.norm_coe_le_norm _
        _ = (t:ℝ) * ‖β‖ := by rw [sub_zero, abs_of_nonneg t.2.1, mul_comm]
        _ ≤ T * ‖β‖ := mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg β))

omit [CompleteSpace E] in
@[simp] lemma intervalPrimitive_apply (hT : (0:ℝ) ≤ T) (β : C(Set.Icc (0:ℝ) T, E))
    (t : Set.Icc (0:ℝ) T) :
    intervalPrimitive hT β t = ∫ s in (0:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT s) := rfl

omit [CompleteSpace E] in

lemma norm_intervalPrimitive_le (hT : (0:ℝ) ≤ T) :
    ‖(intervalPrimitive hT : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))‖ ≤ T :=
  LinearMap.mkContinuous_norm_le _ hT _

omit [CompleteSpace E] in

lemma norm_intervalPrimitive_comp_postcomp_le (hT : (0:ℝ) ≤ T) (A : E →L[ℝ] E) :
    ‖(intervalPrimitive hT).comp (postcomp A)‖ ≤ T * ‖A‖ := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul (norm_intervalPrimitive_le hT) (norm_postcomp_le A) (norm_nonneg _) hT

omit [CompleteSpace E] in

lemma norm_intervalPrimitive_comp_postcompCurve_le (hT : (0:ℝ) ≤ T)
    (A : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)) :
    ‖(intervalPrimitive hT).comp (postcompCurve A)‖ ≤ T * ‖A‖ := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul (norm_intervalPrimitive_le hT) (norm_postcompCurve_le A) (norm_nonneg _) hT

def picardResidual (hT : (0:ℝ) ≤ T) (f : E → E) :
    E × C(Set.Icc (0:ℝ) T, E) → C(Set.Icc (0:ℝ) T, E) := fun q =>
  q.2 - ContinuousMap.const _ q.1 - intervalPrimitive hT (superposition f q.2)

omit [CompleteSpace E] in
@[simp] lemma picardResidual_apply (hT : (0:ℝ) ≤ T) (f : E → E) (x : E)
    (α : C(Set.Icc (0:ℝ) T, E)) :
    picardResidual hT f (x, α)
      = α - ContinuousMap.const _ x - intervalPrimitive hT (superposition f α) := rfl

theorem picardResidual_eq_zero_of_hasDerivWithinAt
    (hT : 0 < T) {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {x : E} {α : ℝ → E}
    (hα0 : α 0 = x)
    (hmem : ∀ t ∈ Set.Icc (0:ℝ) T, α t ∈ u)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α (f (α t)) (Set.Icc (0:ℝ) T) t)
    (σ : C(Set.Icc (0:ℝ) T, E)) (hσ : ∀ t : Set.Icc (0:ℝ) T, σ t = α t) :
    picardResidual hT.le f (x, σ) = 0 := by
  have hσmem : ∀ t : Set.Icc (0:ℝ) T, σ t ∈ u := fun t => by
    rw [hσ t]; exact hmem t t.2
  have hNσ : ∀ t' : Set.Icc (0:ℝ) T, superposition f σ t' = f (σ t') :=
    superposition_apply_of_continuousOn hf σ hσmem
  have hαcont : ContinuousOn α (Set.Icc 0 T) := fun s hs => (hd s hs).continuousWithinAt
  ext t
  have key : (∫ s in (0:ℝ)..(t:ℝ), superposition f σ (Set.projIcc 0 T hT.le s))
      = α t - x := by
    have h1 : (∫ s in (0:ℝ)..(t:ℝ), superposition f σ (Set.projIcc 0 T hT.le s))
        = ∫ s in (0:ℝ)..(t:ℝ), f (α s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le t.2.1] at hs
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
      rw [hNσ, Set.projIcc_of_mem hT.le hsT, hσ]
    rw [h1, intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.2.1
      (hαcont.mono (Set.Icc_subset_Icc le_rfl t.2.2)) ?_ ?_, hα0]
    · intro s hs
      have hsT : s < T := hs.2.trans_le t.2.2
      exact (hd s ⟨hs.1.le, hsT.le⟩).mono_of_mem_nhdsWithin
        (Set.ordConnected_Icc.mem_nhdsGT ⟨hs.1.le, hsT.le⟩
          (Set.right_mem_Icc.mpr hT.le) hsT)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le t.2.1]
      exact hf.comp (hαcont.mono (Set.Icc_subset_Icc le_rfl t.2.2))
        fun s hs => hmem s ⟨hs.1, hs.2.trans t.2.2⟩
  simp only [picardResidual_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.zero_apply, intervalPrimitive_apply, key, hσ t]
  abel

end Poincare.ODE.Parameter
