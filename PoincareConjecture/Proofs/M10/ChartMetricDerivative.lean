import PoincareConjecture.Proofs.M10.ChartMetricSmooth

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackMetricForm_symm (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (y v w : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricForm g f y v w = pullbackMetricForm g f y w v :=
  g.symm _ _ _

theorem fderiv_bilinear_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E} (hB : DifferentiableAt ℝ B y)
    (d v w : E) :
    fderiv ℝ (fun z ↦ B z v w) y d = fderiv ℝ B y d v w := by
  have hd := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).clm_apply
    (hasFDerivAt_const w y)
  have heq := congrArg (fun L : E →L[ℝ] ℝ ↦ L d) hd.fderiv
  simpa only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] using heq

theorem pullbackMetricForm_fderiv_symm (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {y : EuclideanSpace ℝ (Fin n)}
    (hB : DifferentiableAt ℝ (pullbackMetricForm g f) y)
    (d v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (pullbackMetricForm g f) y d v w =
      fderiv ℝ (pullbackMetricForm g f) y d w v := by
  rw [← fderiv_bilinear_apply hB d v w, ← fderiv_bilinear_apply hB d w v]
  congr 2
  funext z
  exact pullbackMetricForm_symm g f z v w

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricForm_fderiv_apply (g : RiemannianMetric n M) (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (d v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (pullbackMetricForm g (extChartAt (𝓡 n) q₀).symm) y d v w =
      mvfderiv (𝓡 n) (fun q ↦ g.inner q
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) v q)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) w q))
        ((extChartAt (𝓡 n) q₀).symm y)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) d
          ((extChartAt (𝓡 n) q₀).symm y)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := extChartAt (𝓡 n) q₀
  let m := fun q ↦ g.inner q
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) v q)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) w q)
  have hq : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source := by
    simpa only [e, extChartAt_source] using e.map_target hy
  have hm : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) m (e.symm y) :=
    ((preferredField_contMDiffAt_of_mem q₀ v hq).inner_bundle
      (preferredField_contMDiffAt_of_mem q₀ w hq)).mdifferentiableAt (by simp)
  have hB := ((chartMetricForm_contDiffOn g q₀).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)).differentiableAt (by simp)
  have heq : (fun z ↦ pullbackMetricForm g e.symm z v w) =ᶠ[𝓝 y] m ∘ e.symm := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy] with z hz
    exact chartMetricForm_apply g q₀ hz v w
  rw [← fderiv_bilinear_apply hB d v w, heq.fderiv_eq]
  have h := preferredField_scalar_derivative q₀ d hq hm
  rw [e.right_inv hy] at h
  exact h

end PoincareConjecture.M10
