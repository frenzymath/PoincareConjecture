import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.LocalCalculus
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Pullback










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M28

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contMDiffAt_tensor_apply_along
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {f : E → M} {x : E}
    {X : Fin k → (y : E) → TangentSpace (𝓡 n) (f y)}
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ f x)
    (hX : ∀ i, ContMDiffAt 𝓘(ℝ, E) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f y) (X i y)) x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun y => T (f y) (fun i => X i y)) x := by
  classical
  let F := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt F V (f x)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let Z := e.localFrame b
  let C (i : Fin k) (j : Fin n) (y : E) :=
    b.repr (e (TotalSpace.mk' F (f y) (X i y))).2 j
  have hx : f x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V (f x)
  have hC (i : Fin k) (j : Fin n) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (C i j) x := by
    have hcoords := (e.contMDiffAt_iff (e.mem_source.mpr hx)).mp (hX i)
    exact (b.coord j).toContinuousLinearMap.contMDiff.contMDiffAt.comp x hcoords.2
  have hZ (a : Fin k → Fin n) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun y => T (f y) (fun i => Z (a i) (f y))) x := by
    exact ((hT.2 e.baseSet e.open_baseSet (fun i => Z (a i))
      (fun i => e.contMDiffOn_localFrame_baseSet ∞ b (a i))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).comp x hf
  have hsum : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ a : Fin k → Fin n,
        (∏ i, C i (a i) y) * T (f y) (fun i => Z (a i) (f y))) x :=
    ContMDiffAt.sum fun a _ =>
      (ContMDiffAt.prod fun i _ => hC i (a i)).mul (hZ a)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)]
    with y hy
  obtain ⟨A, hA⟩ := hT.1 (f y)
  have hdecomp (i : Fin k) :
      X i y = ∑ j : Fin n, C i j y • Z j (f y) := by
    simpa [C, Z, e.localFrame_apply_of_mem_baseSet b hy,
      Bundle.Trivialization.basisAt] using
      ((e.basisAt b hy).sum_repr (X i y)).symm
  simp_rw [hA]
  rw [show (fun i => X i y) =
      (fun i => ∑ j : Fin n, C i j y • Z j (f y)) from funext hdecomp]
  rw [A.map_sum]
  simp only [A.map_smul_univ, smul_eq_mul]



theorem contDiffAt_covariantTensor_pullback
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ f x) (v : Fin k → E) :
    ContDiffAt ℝ ∞
      (fun y => T (f y) (fun i => mfderiv 𝓘(ℝ, E) (𝓡 n) f y (v i))) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_tensor_apply_along hT hf
  intro i
  exact RiemannianMetric.contMDiffAt_mfderiv_const_vector hf (v i)



theorem isSmoothCovariantTensor_pullback
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {f : EuclideanSpace ℝ (Fin n) → M}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f) :
    IsSmoothCovariantTensor
      (fun (y : EuclideanSpace ℝ (Fin n))
        (v : Fin k → TangentSpace (𝓡 n) y) =>
        T (f y) (fun i => mfderiv (𝓡 n) (𝓡 n) f y (v i))) := by
  constructor
  · intro y
    obtain ⟨A, hA⟩ := hT.1 (f y)
    exact ⟨A.compLinearMap (fun _ =>
      (mfderiv (𝓡 n) (𝓡 n) f y).toLinearMap), fun v => hA _⟩
  · intro U hU X hX y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_tensor_apply_along hT (hf y)
    intro i
    exact ((hf y).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      ((hX i).contMDiffAt (hU.mem_nhds hy)) (hf y)

end PoincareConjecture.M28
