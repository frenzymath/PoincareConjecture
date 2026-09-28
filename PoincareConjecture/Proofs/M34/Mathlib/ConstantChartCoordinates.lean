import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Bundle
open scoped Manifold ContDiff Bundle



theorem constantChart_source {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (hchart : ∀ x y : M, chartAt H x = chartAt H y)
    (p : M) : (chartAt H p).source = univ := by
  apply eq_univ_of_forall
  intro x
  rw [hchart p x]
  exact mem_chart_source _ x

section ConstantChartTensors

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners 𝕜 E H) [ChartedSpace H M] [IsManifold I 1 M]
    (hchart : ∀ x y : M, chartAt H x = chartAt H y)

include hchart



theorem constantChart_tangent_baseSet (p : M) :
    (trivializationAt E (TangentSpace I) p).baseSet = univ := by
  rw [TangentBundle.trivializationAt_baseSet, constantChart_source hchart]



theorem constantChart_tangent_symmL (p x : M) :
    (trivializationAt E (TangentSpace I) p).symmL 𝕜 x =
      ContinuousLinearMap.id 𝕜 E := by
  have hx : x ∈ (chartAt H p).source := by
    rw [constantChart_source hchart]
    trivial
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  have hc : achart H p = achart H x := Subtype.ext (hchart p x)
  rw [hc]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore I M).coordChange_self
    (achart H x) x (mem_chart_source _ x) v



theorem constantChart_tangent_forward (p x : M) :
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt 𝕜 x =
      ContinuousLinearMap.id 𝕜 E := by
  have hx : x ∈ (chartAt H p).source := by
    rw [constantChart_source hchart]
    trivial
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  have hc : achart H p = achart H x := Subtype.ext (hchart p x)
  rw [hc]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore I M).coordChange_self
    (achart H x) x (mem_chart_source _ x) v



theorem constantChart_tangent_coordinates (p x : M) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) p) (TotalSpace.mk' E x v) = (x, v) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [constantChart_tangent_baseSet I hchart]
    trivial
  have hh := (trivializationAt E (TangentSpace I) p).apply_mk_symm hx v
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hx,
    constantChart_tangent_symmL I hchart] at hh
  exact hh



theorem constantChart_bilinear_coordinates (p x : M) (B : E →L[𝕜] E →L[𝕜] 𝕜) :
    (trivializationAt (E →L[𝕜] E →L[𝕜] 𝕜)
      (fun y : M => TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] 𝕜) p)
      (TotalSpace.mk' (E →L[𝕜] E →L[𝕜] 𝕜) x B) = (x, B) := by
  have hx : x ∈ (trivializationAt (E →L[𝕜] 𝕜)
      (fun y : M => TangentSpace I y →L[𝕜] 𝕜) p).baseSet := by
    rw [hom_trivializationAt_baseSet, constantChart_tangent_baseSet I hchart]
    exact ⟨mem_univ _, by simp⟩
  rw [hom_trivializationAt_apply]
  congr 1
  ext v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
    Function.comp_apply, constantChart_tangent_symmL I hchart]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx]
  simp +instances [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    constantChart_tangent_symmL I hchart]
  rfl



theorem constantChart_endomorphism_coordinates (p x : M) (B : E →L[𝕜] E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I)
      E (TangentSpace I) p x p x B = B := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    constantChart_tangent_symmL I hchart, constantChart_tangent_forward I hchart]
  rfl



theorem constantChart_vectorBilinear_inCoordinates (p x : M) (B : E →L[𝕜] E →L[𝕜] E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[𝕜] E)
      (fun y : M => TangentSpace I y →L[𝕜] TangentSpace I y)
      p x p x B = B := by
  have hx : x ∈ (trivializationAt (E →L[𝕜] E)
      (fun y : M => TangentSpace I y →L[𝕜] TangentSpace I y) p).baseSet := by
    rw [hom_trivializationAt_baseSet, constantChart_tangent_baseSet I hchart]
    exact ⟨mem_univ _, mem_univ _⟩
  ext v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
    Function.comp_apply, constantChart_tangent_symmL I hchart]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx]
  rw [hom_trivializationAt_apply, constantChart_endomorphism_coordinates I hchart]
  rfl



theorem constantChart_vectorBilinear_coordinates (p x : M) (B : E →L[𝕜] E →L[𝕜] E) :
    (trivializationAt (E →L[𝕜] E →L[𝕜] E) (fun y : M => TangentSpace I y →L[𝕜]
      TangentSpace I y →L[𝕜] TangentSpace I y) p)
      (TotalSpace.mk' (E →L[𝕜] E →L[𝕜] E) x B) = (x, B) := by
  rw [hom_trivializationAt_apply, constantChart_vectorBilinear_inCoordinates I hchart]



theorem constantChart_vectorTrilinear_coordinates (p x : M)
    (B : E →L[𝕜] E →L[𝕜] E →L[𝕜] E) :
    (trivializationAt (E →L[𝕜] E →L[𝕜] E →L[𝕜] E)
      (fun y : M => TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜]
        TangentSpace I y →L[𝕜] TangentSpace I y) p)
          (TotalSpace.mk' (E →L[𝕜] E →L[𝕜] E →L[𝕜] E) x B) = (x, B) := by
  have hx : x ∈ (trivializationAt (E →L[𝕜] E →L[𝕜] E)
      (fun y : M => TangentSpace I y →L[𝕜]
        TangentSpace I y →L[𝕜] TangentSpace I y) p).baseSet := by
    simp only [hom_trivializationAt_baseSet, constantChart_tangent_baseSet I hchart,
      mem_inter_iff, mem_univ, and_self]
  rw [hom_trivializationAt_apply]
  congr 1
  ext u v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
    Function.comp_apply, constantChart_tangent_symmL I hchart]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx]
  rw [hom_trivializationAt_apply, constantChart_vectorBilinear_inCoordinates I hchart]
  rfl

end ConstantChartTensors



theorem constantChart_contMDiff_const_field
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners 𝕜 E H) [ChartedSpace H M] [IsManifold I ∞ M]
    (hchart : ∀ x y : M, chartAt H x = chartAt H y) (v : E) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x v) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  simp only [constantChart_tangent_coordinates I hchart]
  exact contMDiffAt_const
