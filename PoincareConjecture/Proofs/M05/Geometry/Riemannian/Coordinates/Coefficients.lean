
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Metric.Pullback
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.MetricDuality
import Mathlib.Geometry.Manifold.ContMDiff.Atlas








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


noncomputable def pullbackCoefficients (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) (f x) :=
    mfderiv (𝓡 n) (𝓡 n) f x
  exact ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 n) (f x)) (F := TangentSpace (𝓡 n) (f x)) (G := ℝ)
    (E' := EuclideanSpace ℝ (Fin n)) (F' := EuclideanSpace ℝ (Fin n))
    (g.inner (f x)) A A


theorem contDiffAt_pullbackCoefficients (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) :
    ContDiffAt ℝ ∞ (g.pullbackCoefficients f) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_of_apply
  intro v
  apply contMDiffAt_clm_of_apply
  intro w
  exact (g.contDiffAt_pullback_inner hf v w).contMDiffAt


theorem isInvertible_pullbackCoefficients (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    (g.pullbackCoefficients f x).IsInvertible := by
  let B := g.pullbackCoefficients f x
  have hinj : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro v hv
    by_contra hne
    have hAv : mfderiv (𝓡 n) (𝓡 n) f x v ≠ 0 := by
      intro hzero
      exact hne (hf (by simpa using hzero))
    have hpos := g.pos (f x) _ hAv
    have heq := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hv
    change g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x v) = 0 at heq
    exact (ne_of_gt hpos) heq
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toLinearEquiv.finrank_eq
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩


theorem contDiffOn_chartCoefficients (g : RiemannianMetric n M) (p : M) :
    ContDiffOn ℝ ∞ (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      (extChartAt (𝓡 n) p).target := by
  intro x hx
  exact (g.contDiffAt_pullbackCoefficients
    ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx))).contDiffWithinAt


theorem isInvertible_chartCoefficients (g : RiemannianMetric n M) (p : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) p).target) :
    (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).IsInvertible := by
  apply g.isInvertible_pullbackCoefficients
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx
  have hleft : Function.LeftInverse
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) ((extChartAt (𝓡 n) p).symm x))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x) := by
    intro v
    have h := congrArg (fun L => L v) hcomp
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    exact h
  exact hleft.injective

end PoincareConjecture.RiemannianMetric
