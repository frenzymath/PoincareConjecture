import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_UniformCoordinateJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundModelCoordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)





theorem local_bilinear_covariant_norm_eq_pullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 E} {h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : E,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v))
    {A : E → E →L[ℝ] E →L[ℝ] ℝ} (hA : ContDiffOn ℝ ∞ A U)
    {T : CovariantTensorEvaluation 3 M 2} (hT : IsSmoothCovariantTensor T)
    (hAT : ∀ y ∈ U, ∀ v : Fin 2 → E,
      A y (v 0) (v 1) - g.inner y (v 0) (v 1) =
        T (f y) (fun i => mfderiv (𝓡 3) (𝓡 3) f y (v i)))
    (j : ℕ) {x : E} (hx : x ∈ U) :
    g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
      (fun y v => A y (v 0) (v 1) - g.inner y (v 0) (v 1)) j) x =
      h.tensorNorm (D'.iteratedCovariantTensorDerivative T j) (f x) := by
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  obtain ⟨B, hB, heq⟩ := exists_comparison_smooth_germ hU (hA.sub hg.contDiffOn) hx
  let S : CovariantTensorEvaluation 3 E 2 := fun y v => B y (v 0) (v 1)
  have hS : IsSmoothCovariantTensor S := comparison_bilinear_isSmooth hB
  have hSeq : S =ᶠ[𝓝 x]
      (fun (y : E) (v : Fin 2 → E) => A y (v 0) (v 1) - g.inner y (v 0) (v 1)) := by
    filter_upwards [heq] with y hy
    funext v
    change B y (v 0) (v 1) = _
    rw [hy]
    rfl
  have hjet := (comparison_iteratedCovariantTensorDerivative_eventuallyEq D hSeq j).self_of_nhds
  have hnorm : g.tensorNorm (D.iteratedCovariantTensorDerivative S j) x =
      g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => A y (v 0) (v 1) - g.inner y (v 0) (v 1)) j) x := by
    unfold RiemannianMetric.tensorNorm
    rw [hjet]
    rfl
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hSeq)
  have hsub : V ⊆ U := fun y hy => (hV hy).1
  rw [← hnorm]
  apply tensorNorm_iterated_eq_of_metric_pullback D D' hVo (hf.mono hsub)
    (fun y hy => hinv y (hsub hy)) (fun y hy => hmetric y (hsub hy)) hS hT
    (fun y hy v => ?_) j hxV
  rw [(hV hy).2]
  exact hAT y (hsub hy) v

end PoincareConjecture.M44
