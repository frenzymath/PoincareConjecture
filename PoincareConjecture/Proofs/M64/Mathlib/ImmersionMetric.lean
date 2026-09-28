import PoincareConjecture.Proofs.M64.Mathlib.PositiveMetricExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Pullback





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



def m64ImmersionCoefficients (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin m) → M) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  exact ContinuousLinearMap.bilinearComp (g.inner (f x))
    (mfderiv (𝓡 m) (𝓡 n) f x) (mfderiv (𝓡 m) (𝓡 n) f x)



theorem m64_contDiffAt_immersionCoefficients (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin m) → M} {x : EuclideanSpace ℝ (Fin m)}
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f x) :
    ContDiffAt ℝ ∞ (m64ImmersionCoefficients g f) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_of_apply
  intro v
  apply contMDiffAt_clm_of_apply
  intro w
  have hg := (g.contMDiff (f x)).comp x hf
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply] at hh
  convert! hh using 1





theorem m64_exists_induced_metric_near (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin m) → M} {S U : Set (EuclideanSpace ℝ (Fin m))}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) ∞ f U)
    (hinj : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    ∃ (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))) (_D : LeviCivitaData h),
      ∀ x ∈ S, ∀ᶠ y in 𝓝 x, ∀ v w,
        h.inner y v w = g.inner (f y) (mfderiv (𝓡 m) (𝓡 n) f y v)
          (mfderiv (𝓡 m) (𝓡 n) f y w) := by
  have hB : ContDiffOn ℝ ∞ (m64ImmersionCoefficients g f) U := by
    intro x hx
    exact (m64_contDiffAt_immersionCoefficients g
      ((hf x hx).contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  have hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < m64ImmersionCoefficients g f x v v := by
    intro x hx v hv
    have hAv : mfderiv (𝓡 m) (𝓡 n) f x v ≠ 0 := by
      intro hz
      exact hv ((hinj x hx) (by simpa using hz))
    exact g.pos (f x) _ hAv
  obtain ⟨h, D, heq⟩ := m64_exists_metric_eq_nhds_of_isClosed hS hU hSU
    (m64ImmersionCoefficients g f) hB
    (fun x _ v w => g.symm (f x) _ _) hpos
  refine ⟨h, D, ?_⟩
  intro x hx
  filter_upwards [heq x hx] with y hy
  intro v w
  exact congrArg (fun B => B v w) hy

end PoincareConjecture
