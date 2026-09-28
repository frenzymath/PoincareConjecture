import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.BlockContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedReaction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Laplacian.Linearity






set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Matrix Filter Bundle

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def metricTwoFormIdentity (g : RiemannianMetric n M) :
    CovariantTensorEvaluation n M 4 := fun x v =>
  (g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3) -
    g.inner x (v 0) (v 3) * g.inner x (v 1) (v 2)) / 2

lemma metric_isSmoothCovariantTensor (g : RiemannianMetric n M) :
    IsSmoothCovariantTensor (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) := by
  constructor
  · intro x
    refine ⟨{ toFun := fun v => g.inner x (v 0) (v 1)
              map_update_add' := ?_
              map_update_smul' := ?_ }, fun _ => rfl⟩
    · intro _ v i a b
      fin_cases i <;> simp [Function.update, map_add]
    · intro _ v i c a
      fin_cases i <;> simp [Function.update, map_smul]
  · intro U hU X hX x hx
    have h := ((g.contMDiff x).clm_bundle_apply
      ((hX 0 x hx).contMDiffAt (hU.mem_nhds hx))).clm_bundle_apply
      ((hX 1 x hx).contMDiffAt (hU.mem_nhds hx))
    exact (contMDiffAt_totalSpace.mp h).2.contMDiffWithinAt

lemma scalar_metric_isSmoothCovariantTensor {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) :
    IsSmoothCovariantTensor (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      φ x * g.inner x (v 0) (v 1)) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := (metric_isSmoothCovariantTensor g).1 x
    exact ⟨φ x • A, fun v => by simp only [_root_.smul_apply, smul_eq_mul, ← hA]⟩
  · intro U hU X hX
    exact hφ.contMDiffOn.mul ((metric_isSmoothCovariantTensor g).2 U hU X hX)

lemma metricTwoFormIdentity_isSmooth (g : RiemannianMetric n M) :
    IsSmoothCovariantTensor (metricTwoFormIdentity g) := by
  have hG := metric_isSmoothCovariantTensor g
  have hGG := isSmoothCovariantTensor_tensorProduct hG hG
  have h := ((hGG.perm (Equiv.swap 1 2)).sub
    (hGG.perm (Equiv.swap 1 3))).const_mul (1 / 2)
  convert h using 1
  funext x v
  simp only [tensorProduct, Function.comp_apply]
  change metricTwoFormIdentity g x v =
    1 / 2 * (g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3) -
      g.inner x (v 0) (v 3) * g.inner x (v 2) (v 1))
  dsimp only [metricTwoFormIdentity]
  rw [g.symm x (v 2) (v 1)]
  ring

private lemma exists_metric_radial_fields (D : LeviCivitaData g) (x : M) :
    ∃ E : TangentSpace (𝓡 n) x → (y : M) → TangentSpace (𝓡 n) y,
      (∀ v, E v x = v) ∧
      (∀ v, ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (E v)) x) ∧
      (∀ v a, D.connection (E v) x a = 0) ∧
      (∀ v a, D.connection (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) (E v)) x a = 0) ∧
      (∀ᶠ y in 𝓝 x, ∀ v w, g.inner y (E v y) (E w y) = g.inner x v w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, Y, hr, _, hY, hinit, _, hfirst, hsecond, P, hP⟩ :=
    D.exists_radialParallelIsometries_with_jets x
  refine ⟨fun v => LeviCivitaData.fieldFromCenteredCoordinates x (Y v),
    hinit, ?_, hfirst, hsecond, ?_⟩
  · intro v
    exact LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates x
      (hY v).contDiffAt (mem_extChartAt_source x)
  · filter_upwards [(LeviCivitaData.isOpen_radialNeighborhood (n := n) x r).mem_nhds
      (LeviCivitaData.mem_radialNeighborhood (n := n) x hr)] with y hy v w
    rw [← hP ⟨y, hy⟩ v, ← hP ⟨y, hy⟩ w]
    exact (P ⟨y, hy⟩).inner_map_map v w



lemma tensorLaplacian_scalar_metric (D : LeviCivitaData g) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (x : M)
    (v : Fin 2 → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      φ y * g.inner y (z 0) (z 1)) x v =
        D.laplacian φ x * g.inner x (v 0) (v 1) := by
  obtain ⟨E, hinit, hE, hfirst, hsecond, hinner⟩ := exists_metric_radial_fields D x
  have h := D.tensorLaplacian_eq_laplacian_of_zero_jets
    (scalar_metric_isSmoothCovariantTensor (g := g) hφ) (fun i => E (v i)) x
    (fun i => hE (v i)) (fun i => hfirst (v i)) (fun i => hsecond (v i))
  simp only [hinit] at h
  rw [h]
  have he : (fun y => φ y * g.inner y (E (v 0) y) (E (v 1) y)) =ᶠ[𝓝 x]
      (fun y => g.inner x (v 0) (v 1) * φ y) := by
    filter_upwards [hinner] with y hy
    rw [hy]
    exact mul_comm _ _
  rw [D.laplacian_eq_of_eventuallyEq he, D.laplacian_const_mul, mul_comm]


lemma covariantTensorDerivative_metricTwoFormIdentity (D : LeviCivitaData g) :
    D.covariantTensorDerivative (metricTwoFormIdentity g) = fun _ _ => 0 := by
  funext x v
  obtain ⟨E, hinit, hE, hfirst, _, hinner⟩ := exists_metric_radial_fields D x
  have h := covariantTensorDerivative_eq_mvfderiv_of_zero_jets D
    (metricTwoFormIdentity_isSmooth g) (fun i => E (v i.succ)) x
    (fun i => hE (v i.succ)) (fun i => hfirst (v i.succ)) (v 0)
  have hv : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; fin_cases i <;> rfl
  simp only [hinit, hv] at h
  rw [h]
  have he : (fun y => metricTwoFormIdentity g y (fun i => E (v i.succ) y)) =ᶠ[𝓝 x]
      (fun _ => metricTwoFormIdentity g x (fun i => v i.succ)) := by
    filter_upwards [hinner] with y hy
    simp only [metricTwoFormIdentity, hy]
  unfold mvfderiv
  rw [he.mfderiv_eq]
  simp

lemma tensorLaplacian_metricTwoFormIdentity (D : LeviCivitaData g) :
    D.tensorLaplacian (metricTwoFormIdentity g) = fun _ _ => 0 := by
  funext x v
  simp only [LeviCivitaData.tensorLaplacian,
    LeviCivitaData.iteratedCovariantTensorDerivative,
    covariantTensorDerivative_metricTwoFormIdentity]
  simp [LeviCivitaData.covariantTensorDerivative, mvfderiv]



noncomputable def tensorBlockDiffusion {I : Type} [Fintype I]
    (D : LeviCivitaData g) (R : CovariantTensorEvaluation n M 4)
    (P : CovariantTensorEvaluation n M 3) (B : CovariantTensorEvaluation n M 2)
    (x : M) (v : I → TangentSpace (𝓡 n) x) (U : I → I → ℝ) (W : I → ℝ)
    (A : I → I → TangentSpace (𝓡 n) x) : ℝ :=
  (∑ a, ∑ b, D.tensorLaplacian B x ![v a, v b] * W a * W b) +
    2 * (∑ a, ∑ b, ∑ c, D.tensorLaplacian P x ![v a, v b, v c] * U a b * W c) +
    (∑ a, ∑ b, ∑ c, ∑ d,
      D.tensorLaplacian R x ![v a, v b, v c, v d] * U a b * U c d) +
    4 * (∑ a, ∑ b, ∑ c, ∑ d,
      U a b * D.covariantTensorDerivative R x ![A c d, v a, v b, v c, v d]) +
    4 * (∑ a, ∑ b, ∑ c,
      W c * D.covariantTensorDerivative P x ![A a b, v a, v b, v c]) +
    2 * (∑ a, ∑ b, ∑ c, ∑ d,
      R x ![v a, v b, v c, v d] * g.inner x (A a b) (A c d))



lemma tensorBlockDiffusion_perturb {I : Type} [Fintype I]
    (D : LeviCivitaData g) {R : CovariantTensorEvaluation n M 4}
    {P : CovariantTensorEvaluation n M 3} {B : CovariantTensorEvaluation n M 2}
    (hR : IsSmoothCovariantTensor R) (hB : IsSmoothCovariantTensor B)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (ψ : ℝ)
    (x : M) (v : I → TangentSpace (𝓡 n) x) (U : I → I → ℝ) (W : I → ℝ)
    (A : I → I → TangentSpace (𝓡 n) x) :
    tensorBlockDiffusion D (fun y z => R y z + ψ * metricTwoFormIdentity g y z) P
        (fun y z => B y z + φ y * g.inner y (z 0) (z 1)) x v U W A =
      tensorBlockDiffusion D R P B x v U W A +
        D.laplacian φ x * (∑ a, ∑ b, g.inner x (v a) (v b) * W a * W b) +
        2 * ψ * (∑ a, ∑ b, ∑ c, ∑ d,
          metricTwoFormIdentity g x ![v a, v b, v c, v d] *
            g.inner x (A a b) (A c d)) := by
  have hI := metricTwoFormIdentity_isSmooth g
  have hφg := scalar_metric_isSmoothCovariantTensor (g := g) hφ
  have hψI := hI.const_mul ψ
  have hDR := D.covariantTensorDerivative_isSmooth hR
  have hDB := D.covariantTensorDerivative_isSmooth hB
  have hDI := D.covariantTensorDerivative_isSmooth hI
  have hDφg := D.covariantTensorDerivative_isSmooth hφg
  have hDψI := D.covariantTensorDerivative_isSmooth hψI
  unfold tensorBlockDiffusion
  simp only [D.tensorLaplacian_add hB hφg hDB hDφg,
    D.tensorLaplacian_add hR hψI hDR hDψI,
    D.tensorLaplacian_const_mul hI hDI,
    tensorLaplacian_scalar_metric D hφ, tensorLaplacian_metricTwoFormIdentity,
    D.covariantTensorDerivative_add hR hψI,
    D.covariantTensorDerivative_const_mul hI,
    covariantTensorDerivative_metricTwoFormIdentity,
    mul_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring



theorem perturbed_tensor_block_diffusion_nonneg_at_null [T2Space M]
    {I : Type} [Fintype I] (D : LeviCivitaData g)
    {R : CovariantTensorEvaluation n M 4} {P : CovariantTensorEvaluation n M 3}
    {B : CovariantTensorEvaluation n M 2}
    (hR : IsSmoothCovariantTensor R) (hP : IsSmoothCovariantTensor P)
    (hB : IsSmoothCovariantTensor B)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (ψ : ℝ)
    (x : M) (v : I → TangentSpace (𝓡 n) x)
    (hpos : ∀ᶠ y in 𝓝 x, ∀ e : I → TangentSpace (𝓡 n) y,
      (Matrix.fromBlocks (fun ab cd : I × I =>
        R y ![e ab.1, e ab.2, e cd.1, e cd.2] +
          ψ * metricTwoFormIdentity g y ![e ab.1, e ab.2, e cd.1, e cd.2])
        (fun ab c => P y ![e ab.1, e ab.2, e c])
        (fun a bc => P y ![e bc.1, e bc.2, e a])
        (fun a b => B y ![e a, e b] + φ y * g.inner y (e a) (e b))).PosSemidef)
    (U : I → I → ℝ) (W : I → ℝ)
    (hnull : (∑ a, ∑ b, (B x ![v a, v b] + φ x * g.inner x (v a) (v b)) * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P x ![v a, v b, v c] * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        (R x ![v a, v b, v c, v d] +
          ψ * metricTwoFormIdentity g x ![v a, v b, v c, v d]) * U a b * U c d) = 0)
    (A : I → I → TangentSpace (𝓡 n) x) :
    0 ≤ tensorBlockDiffusion D R P B x v U W A +
      D.laplacian φ x * (∑ a, ∑ b, g.inner x (v a) (v b) * W a * W b) +
      2 * ψ * (∑ a, ∑ b, ∑ c, ∑ d,
        metricTwoFormIdentity g x ![v a, v b, v c, v d] *
          g.inner x (A a b) (A c d)) := by
  have h := tensor_block_diffusion_nonneg_at_null D
    (hR.add ((metricTwoFormIdentity_isSmooth g).const_mul ψ)) hP
    (hB.add (scalar_metric_isSmoothCovariantTensor (g := g) hφ)) x v hpos U W hnull A
  change 0 ≤ tensorBlockDiffusion D _ P _ x v U W A at h
  rwa [tensorBlockDiffusion_perturb D hR hB hφ ψ] at h

lemma metric_inner_orthonormalBasis (g : RiemannianMetric n M) (x : M)
    (a b : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    g.inner x (g.orthonormalBasis x a) (g.orthonormalBasis x b) =
      if a = b then 1 else 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (g.orthonormalBasis x).inner_eq_ite a b

lemma metricTwoFormIdentity_orthonormalBasis (g : RiemannianMetric n M) (x : M)
    (a b c d : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    metricTwoFormIdentity g x ![g.orthonormalBasis x a, g.orthonormalBasis x b,
      g.orthonormalBasis x c, g.orthonormalBasis x d] = twoFormIdentity a b c d := by
  simp only [metricTwoFormIdentity, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, metric_inner_orthonormalBasis, twoFormIdentity]
  split_ifs <;> simp_all

private lemma metric_basis_quadratic (g : RiemannianMetric n M) (x : M)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    (∑ a, ∑ b, g.inner x (g.orthonormalBasis x a) (g.orthonormalBasis x b) * W a * W b) =
      ∑ a, W a ^ 2 := by
  simp only [metric_inner_orthonormalBasis, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]

private lemma metric_inner_basis_sums (g : RiemannianMetric n M) (x : M)
    (v w : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    g.inner x (∑ e, v e • g.orthonormalBasis x e)
      (∑ e, w e • g.orthonormalBasis x e) = ∑ e, v e * w e := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ (∑ e, v e • g.orthonormalBasis x e)
    (∑ e, w e • g.orthonormalBasis x e) = _
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    (g.orthonormalBasis x).inner_eq_ite, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro e _
  ring

private lemma sum_four_last' {I : Type} [Fintype I] (f : I → I → I → I → ℝ) :
    (∑ a, ∑ c, ∑ d, ∑ e, f a c d e) = ∑ e, ∑ a, ∑ c, ∑ d, f a c d e := by
  calc
    _ = ∑ a, ∑ e, ∑ c, ∑ d, f a c d e := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm_cycle
    _ = _ := Finset.sum_comm

private lemma sum_five_last' {I : Type} [Fintype I] (f : I → I → I → I → I → ℝ) :
    (∑ a, ∑ c, ∑ d, ∑ f', ∑ e, f a c d f' e) =
      ∑ e, ∑ a, ∑ c, ∑ d, ∑ f', f a c d f' e := by
  calc
    _ = ∑ a, ∑ e, ∑ c, ∑ d, ∑ f', f a c d f' e := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_four_last' (f a)
    _ = _ := Finset.sum_comm



lemma metricTwoFormIdentity_jet_quadratic (g : RiemannianMetric n M) (x : M)
    (V : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hV : ∀ e a b, V e a b = -V e b a) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      metricTwoFormIdentity g x ![g.orthonormalBasis x a, g.orthonormalBasis x b,
        g.orthonormalBasis x c, g.orthonormalBasis x d] *
      g.inner x (∑ e, V e a b • g.orthonormalBasis x e)
        (∑ e, V e c d • g.orthonormalBasis x e)) = ∑ e, ∑ a, ∑ b, (V e a b) ^ 2 := by
  simp only [metricTwoFormIdentity_orthonormalBasis, metric_inner_basis_sums, Finset.mul_sum]
  rw [sum_five_last']
  apply Finset.sum_congr rfl
  intro e _
  simpa only [mul_assoc] using twoFormIdentity_quadratic (V e) (hV e)



theorem perturbed_tensor_block_diffusion_nonneg_in_basis [T2Space M]
    (D : LeviCivitaData g)
    {R : CovariantTensorEvaluation n M 4} {P : CovariantTensorEvaluation n M 3}
    {B : CovariantTensorEvaluation n M 2}
    (hR : IsSmoothCovariantTensor R) (hP : IsSmoothCovariantTensor P)
    (hB : IsSmoothCovariantTensor B)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (ψ : ℝ) (x : M)
    (hpos : ∀ᶠ y in 𝓝 x, let b := g.orthonormalBasis y
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) =>
          R y ![b ac.1, b ac.2, b de.1, b de.2] + ψ * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => P y ![b ac.1, b ac.2, b d])
        (fun c de => P y ![b de.1, b de.2, b c])
        (fun a c => B y ![b a, b c] + φ y * (if a = c then 1 else 0))).PosSemidef)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a b, U a b = -U b a)
    (hnull : let b := g.orthonormalBasis x
      (∑ a, ∑ b', B x ![b a, b b'] * W a * W b') +
      2 * (∑ a, ∑ b', ∑ c, P x ![b a, b b', b c] * U a b' * W c) +
      (∑ a, ∑ b', ∑ c, ∑ d, R x ![b a, b b', b c, b d] * U a b' * U c d) +
      φ x * (∑ a, W a ^ 2) + ψ * (∑ a, ∑ b', (U a b') ^ 2) = 0)
    (V : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hV : ∀ e a b, V e a b = -V e b a) :
    0 ≤ tensorBlockDiffusion D R P B x (g.orthonormalBasis x) U W
      (fun a b => ∑ e, V e a b • g.orthonormalBasis x e) +
      D.laplacian φ x * (∑ a, W a ^ 2) + 2 * ψ * (∑ e, ∑ a, ∑ b, (V e a b) ^ 2) := by
  let R' : CovariantTensorEvaluation n M 4 := fun y z => R y z + ψ * metricTwoFormIdentity g y z
  let B' : CovariantTensorEvaluation n M 2 := fun y z => B y z + φ y * g.inner y (z 0) (z 1)
  have hR' : IsSmoothCovariantTensor R' := hR.add ((metricTwoFormIdentity_isSmooth g).const_mul ψ)
  have hB' : IsSmoothCovariantTensor B' := hB.add (scalar_metric_isSmoothCovariantTensor (g := g) hφ)
  have hp : ∀ᶠ y in 𝓝 x, ∀ e : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      TangentSpace (𝓡 n) y,
      (Matrix.fromBlocks (fun ab cd : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
          R' y ![e ab.1, e ab.2, e cd.1, e cd.2])
        (fun ab c => P y ![e ab.1, e ab.2, e c])
        (fun a bc => P y ![e bc.1, e bc.2, e a])
        (fun a b => B' y ![e a, e b])).PosSemidef := by
    filter_upwards [hpos] with y hy e
    apply tensor_block_posSemidef_of_basis g hR' hP hB' y _ e
    simpa only [R', B', metricTwoFormIdentity_orthonormalBasis,
      Matrix.cons_val_zero, Matrix.cons_val_one, metric_inner_orthonormalBasis] using hy
  let b := g.orthonormalBasis x
  have hn : (∑ a, ∑ c, B' x ![b a, b c] * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d, P x ![b a, b c, b d] * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e, R' x ![b a, b c, b d, b e] * U a c * U d e) = 0 := by
    dsimp only [R', B', b, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [metricTwoFormIdentity_orthonormalBasis, add_mul, Finset.sum_add_distrib]
    have hg := metric_basis_quadratic g x W
    have hi := twoFormIdentity_quadratic U hU
    have hg' : (∑ a, ∑ c, φ x * g.inner x (b a) (b c) * W a * W c) =
        φ x * (∑ a, W a ^ 2) := by
      rw [← hg]
      simp only [b, Finset.mul_sum, mul_assoc]
    have hi' : (∑ a, ∑ c, ∑ d, ∑ e, ψ * twoFormIdentity a c d e * U a c * U d e) =
        ψ * (∑ a, ∑ c, (U a c) ^ 2) := by
      rw [← hi]
      simp only [Finset.mul_sum, mul_assoc]
    rw [hg', hi']
    dsimp only at hnull
    linarith only [hnull]
  have h := perturbed_tensor_block_diffusion_nonneg_at_null D hR hP hB hφ ψ x b hp U W hn
    (fun a b => ∑ e, V e a b • g.orthonormalBasis x e)
  simpa only [b, metric_basis_quadratic, metricTwoFormIdentity_jet_quadratic g x V hV] using h



noncomputable def hamiltonSpatialJetQuadratic (D : LeviCivitaData g) (τ : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (V : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) : ℝ :=
  let b := g.orthonormalBasis x
  (∑ a, ∑ c, D.tensorLaplacian (fun y z =>
    hamiltonM D τ y (z 0) (z 1)) x ![b a, b c] * W a * W c) +
    2 * (∑ a, ∑ c, ∑ d,
      D.tensorLaplacian (fun y z => hamiltonP D y
        (z 0) (z 1) (z 2)) x ![b a, b c, b d] * U a c * W d) +
    (∑ a, ∑ c, ∑ d, ∑ e,
      D.tensorLaplacian D.riemannEvaluation x ![b a, b c, b d, b e] * U a c * U d e) +
    4 * (∑ e, ∑ a, ∑ c, ∑ d,
      D.covariantTensorDerivative (fun y z => hamiltonP D y (z 0) (z 1) (z 2))
        x ![b e, b a, b c, b d] * V e a c * W d) +
    4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
        V e a c * U d f) +
    2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      D.curvatureTensor x (b a) (b c) (b d) (b f) * V e a c * V e d f)

private lemma covariantTensorDerivative_cons_sum'
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (w : Fin k → TangentSpace (𝓡 n) x)
    (c : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    D.covariantTensorDerivative T x
      (Fin.cons (∑ e, c e • g.orthonormalBasis x e) w) =
      ∑ e, c e * D.covariantTensorDerivative T x (Fin.cons (g.orthonormalBasis x e) w) := by
  classical
  obtain ⟨L, hL⟩ := (D.covariantTensorDerivative_isSmooth hT).1 x
  rw [← Fin.update_cons_zero (x := (0 : TangentSpace (𝓡 n) x)), hL,
    L.map_update_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [L.map_update_smul]
  simp only [smul_eq_mul, Fin.update_cons_zero, ← hL]

lemma hamiltonSpatialJetQuadratic_eq_tensorBlockDiffusion
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (τ : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (V : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    hamiltonSpatialJetQuadratic D τ x U W V =
      tensorBlockDiffusion D D.riemannEvaluation
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2))
        (fun y z => hamiltonM D τ y (z 0) (z 1)) x (g.orthonormalBasis x) U W
        (fun a c => ∑ e, V e a c • g.orthonormalBasis x e) := by
  let b := g.orthonormalBasis x
  let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
  let A := fun a c => ∑ e, V e a c • b e
  have hP : IsSmoothCovariantTensor P := hamiltonP_isSmoothCovariantTensor D hD
  have hfirstP (a c d) : D.covariantTensorDerivative P x ![A a c, b a, b c, b d] =
      ∑ e, V e a c * D.covariantTensorDerivative P x ![b e, b a, b c, b d] :=
    covariantTensorDerivative_cons_sum' D hP x ![b a, b c, b d] (fun e => V e a c)
  have hfirstR (a c d f) : D.covariantTensorDerivative D.riemannEvaluation x
      ![A d f, b a, b c, b d, b f] =
      ∑ e, V e d f * D.covariantTensorDerivative D.riemannEvaluation x
        ![b e, b d, b f, b a, b c] := by
    rw [D.covariantTensorDerivative_riemannEvaluation_pair_swap hD]
    exact covariantTensorDerivative_cons_sum' D hD.1 x ![b d, b f, b a, b c]
      (fun e => V e d f)
  have hinner (a c d f) : g.inner x (A a c) (A d f) = ∑ e, V e a c * V e d f :=
    metric_inner_basis_sums g x (fun e => V e a c) (fun e => V e d f)
  have hPorder : (∑ a, ∑ c, ∑ d,
      W d * D.covariantTensorDerivative P x ![A a c, b a, b c, b d]) =
      ∑ e, ∑ a, ∑ c, ∑ d,
        D.covariantTensorDerivative P x ![b e, b a, b c, b d] * V e a c * W d := by
    simp only [hfirstP, Finset.mul_sum]
    rw [sum_four_last']
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hRorder : (∑ a, ∑ c, ∑ d, ∑ f,
      U a c * D.covariantTensorDerivative D.riemannEvaluation x ![A d f, b a, b c, b d, b f]) =
      ∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
          V e a c * U d f := by
    simp only [hfirstR, Finset.mul_sum]
    rw [sum_five_last']
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hVorder : (∑ a, ∑ c, ∑ d, ∑ f,
      D.riemannEvaluation x ![b a, b c, b d, b f] * g.inner x (A a c) (A d f)) =
      ∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.curvatureTensor x (b a) (b c) (b d) (b f) * V e a c * V e d f := by
    simp only [hinner, Finset.mul_sum]
    rw [sum_five_last']
    simp only [mul_assoc, LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
  unfold hamiltonSpatialJetQuadratic tensorBlockDiffusion
  rw [hPorder, hRorder, hVorder]
  ring



theorem hamiltonSpatialJetQuadratic_nonneg_perturbed_null [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (τ : ℝ)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (ψ : ℝ) (x : M)
    (hpos : ∀ᶠ y in 𝓝 x, let b := g.orthonormalBasis y
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) =>
          D.curvatureTensor y (b ac.1) (b ac.2) (b de.1) (b de.2) +
            ψ * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => hamiltonP D y (b ac.1) (b ac.2) (b d))
        (fun c de => hamiltonP D y (b de.1) (b de.2) (b c))
        (fun a c => hamiltonM D τ y (b a) (b c) + φ y * (if a = c then 1 else 0))).PosSemidef)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a b, U a b = -U b a)
    (hnull : let b := g.orthonormalBasis x
      (∑ a, ∑ c, hamiltonM D τ x (b a) (b c) * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d, hamiltonP D x (b a) (b c) (b d) * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e, D.curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) +
      φ x * (∑ a, W a ^ 2) + ψ * (∑ a, ∑ c, (U a c) ^ 2) = 0)
    (V : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hV : ∀ e a b, V e a b = -V e b a) :
    0 ≤ hamiltonSpatialJetQuadratic D τ x U W V +
      D.laplacian φ x * (∑ a, W a ^ 2) + 2 * ψ * (∑ e, ∑ a, ∑ b, (V e a b) ^ 2) := by
  rw [hamiltonSpatialJetQuadratic_eq_tensorBlockDiffusion D hD]
  exact perturbed_tensor_block_diffusion_nonneg_in_basis D hD.1
    (hamiltonP_isSmoothCovariantTensor D hD) (hamiltonM_isSmoothCovariantTensor D hD τ)
    hφ ψ x hpos U W hU hnull V hV

end Poincare.RicciFlow.Harnack
