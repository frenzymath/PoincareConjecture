import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletForm
import PoincareConjecture.Proofs.M03.Existence.HilbertParabolicNative
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

instance dirichletValue_separableSpace (K : Set V) :
    TopologicalSpace.SeparableSpace (dirichletValue K) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  let : SecondCountableTopology L2 := inferInstance
  infer_instance

private theorem totallyBounded_testValues {K : Set V} (hK : IsCompact K)
    {S : Set (dirichletValue K)} {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ u ∈ S, ∃ f : supportedTests K,
      u = intoDirichletValue K f ∧ ‖dirichletImage K f‖ ≤ R) :
    TotallyBounded S := by
  apply (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing).mp
  apply EuclideanRellichNative.totallyBounded_supported_C1 hK hR
  · rintro u ⟨v, hv, rfl⟩
    obtain ⟨f, rfl, hfR⟩ := hS v hv
    exact (WithLp.norm_fst_le (dirichletValue K) (dirichletImage K f)).trans hfR
  · rintro u ⟨v, hv, rfl⟩
    obtain ⟨f, rfl, hfR⟩ := hS v hv
    refine ⟨(f : V → ℝ), (f : 𝓢(V, ℝ)).smooth 1,
      (f : 𝓢(V, ℝ)).memLp 2 volume, ?_, f.property, rfl, ?_⟩
    · intro i
      have he : ((∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ)) : 𝓢(V, ℝ)) : V → ℝ) =
          (fun x => fderiv ℝ (f : V → ℝ) x (EuclideanSpace.single i 1)) :=
        funext (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _)
      rw [← he]
      exact (∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).memLp 2 volume
    · have hs := (sq_le_sq₀ (norm_nonneg _) hR).mpr hfR
      have he := dirichletImage_norm_sq K f
      nlinarith only [hs, he, sq_nonneg ‖testValue K f‖]

private theorem totallyBounded_dirichletImage_value {K : Set V} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded
      ((WithLp.fstL 2 ℝ (dirichletValue K) (DirichletGradient n)) ''
        (Set.range (dirichletImage K) ∩ Metric.ball 0 R)) := by
  apply totallyBounded_testValues hK hR
  rintro u ⟨y, ⟨⟨f, rfl⟩, hyR⟩, rfl⟩
  refine ⟨f, rfl, ?_⟩
  exact (show ‖dirichletImage K f‖ < R by
    simpa only [Metric.mem_ball, dist_zero_right] using hyR).le

theorem totallyBounded_dirichletInclusion_closedBall {K : Set V} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded (dirichletInclusion K '' Metric.closedBall 0 R) := by
  let P : DirichletAmbient K →L[ℝ] dirichletValue K :=
    WithLp.fstL 2 ℝ (dirichletValue K) (DirichletGradient n)
  have hc : TotallyBounded
      (P '' (closure (Set.range (dirichletImage K)) ∩ Metric.closedBall 0 R)) :=
    EuclideanRellichNative.totallyBounded_bounded_graph_closure P P.continuous
      (totallyBounded_dirichletImage_value hK (by linarith : 0 ≤ R + 1))
  apply hc.subset
  rintro u ⟨v, hvR, rfl⟩
  exact ⟨(v : DirichletAmbient K), ⟨v.property, hvR⟩, rfl⟩

theorem isCompactOperator_dirichletInclusion {K : Set V} (hK : IsCompact K) :
    IsCompactOperator (dirichletInclusion K) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (dirichletInclusion K).toLinearMap zero_lt_one).mpr
  exact (totallyBounded_dirichletInclusion_closedBall hK zero_le_one).closure.isCompact_of_isClosed
    isClosed_closure

theorem exists_dirichlet_response {K : Set V} (hK : IsCompact K)
    {T : ℝ} (hT : 0 ≤ T) {F : ℝ → dirichletValue K}
    (hF : MemLp F 2 (SpectralHeatNative.timeMeasure T)) :
    ∃ U D A : ℝ → dirichletValue K,
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (SpectralHeatNative.timeMeasure T) ∧
      MemLp A 2 (SpectralHeatNative.timeMeasure T) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, D t + A t = F t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
        HilbertResolventNative.InGeneratorGraph («V» := dirichletForm K)
          (dirichletInclusion K) (U t) (A t)) ∧
      (∫ t, ‖D t‖ ^ 2 ∂SpectralHeatNative.timeMeasure T) +
          (∫ t, ‖A t‖ ^ 2 ∂SpectralHeatNative.timeMeasure T) ≤
        ∫ t, ‖F t‖ ^ 2 ∂SpectralHeatNative.timeMeasure T := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  apply HilbertResolventNative.exists_response («V» := dirichletForm K)
    (H := dirichletValue K) (T := T) (F := F) (dirichletInclusion K)
  · exact isCompactOperator_dirichletInclusion hK
  · exact dirichletInclusion_denseRange K
  · exact norm_dirichletInclusion_le_one K
  · exact hT
  · exact hF

end PoincareConjecture.M35.Uniqueness.Heat
