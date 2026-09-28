import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Regularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isInvertible_mfderiv_of_injective
    {e : EuclideanSpace ℝ (Fin n) → M} {v : EuclideanSpace ℝ (Fin n)}
    (h : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e v)) :
    (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) e v
  have hi : Function.Injective A := h
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem isInvertible_mfderiv_zero_of_chart_derivative
    {e : EuclideanSpace ℝ (Fin n) → M} {p : M}
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e 0) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
      L.toContinuousLinearMap 0) :
    (mfderiv (𝓡 n) (𝓡 n) e 0).IsInvertible := by
  apply isInvertible_mfderiv_of_injective
  intro v w hvw
  apply L.injective
  have hd := mfderiv_comp 0
    (mdifferentiableAt_extChartAt (by rw [he0]; exact mem_chart_source _ _)) he
  rw [mfderiv_eq_fderiv] at hd
  have hd' : L.toContinuousLinearMap =
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (e 0)).comp
        (mfderiv (𝓡 n) (𝓡 n) e 0) := hed.fderiv.symm.trans hd
  have h := congrArg (fun v => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (e 0) v) hvw
  have hv := congrArg (fun A => A v) hd'
  have hw := congrArg (fun A => A w) hd'
  exact hv.trans (h.trans hw.symm)

end PoincareConjecture.RiemannianMetric
