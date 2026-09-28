import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.RicciAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Laplacian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

open PoincareConjecture
open PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {g : RiemannianMetric n M}

noncomputable def tensorHeatOperator (F : RicciFlow n M J)
    {k : ℕ} (T : ℝ → CovariantTensorEvaluation n M k) (t : ℝ)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) : ℝ :=
  deriv (fun s => T s x v) t +
    (F.connection t).ricciTensorAction (T t) x v -
    (F.connection t).tensorLaplacian (T t) x v

private lemma connection_deriv_inner
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u z e : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let A := fun q : TangentSpace (𝓡 n) x => deriv (fun s =>
      (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q) x) t
    (F.metric t).inner x (A z u) e =
      -D.covariantTensorDerivative D.ricciEvaluation x ![u, z, e] -
        D.covariantTensorDerivative D.ricciEvaluation x ![z, u, e] +
        D.covariantTensorDerivative D.ricciEvaluation x ![e, u, z] := by
  dsimp only
  exact F.inner_deriv_connection_extend ht (hC.tensor_calculus n M (F.metric t) (F.connection t))
    x u z e

private lemma tensor_slot_left_eq_sum
    (g : RiemannianMetric n M)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (q w : TangentSpace (𝓡 n) x) :
    T x ![q, w] = ∑ i, g.inner x q (g.orthonormalBasis x i) *
      T x ![g.orthonormalBasis x i, w] := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB⟩ := hT.1 x
  let L := B.toLinearMap ![(0 : TangentSpace (𝓡 n) x), w] 0
  have hL (z : TangentSpace (𝓡 n) x) : L z = T x ![z, w] := by
    simp only [L, MultilinearMap.toLinearMap_apply]
    rw [hB]
    congr 1
    funext i
    fin_cases i <;> rfl
  have h := congrArg L ((g.orthonormalBasis x).sum_repr' q)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp only [hL] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  rfl

private lemma tensor_slot_right_eq_sum
    (g : RiemannianMetric n M)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (v q : TangentSpace (𝓡 n) x) :
    T x ![v, q] = ∑ i, g.inner x q (g.orthonormalBasis x i) *
      T x ![v, g.orthonormalBasis x i] := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB⟩ := hT.1 x
  let L := B.toLinearMap ![v, (0 : TangentSpace (𝓡 n) x)] 1
  have hL (z : TangentSpace (𝓡 n) x) : L z = T x ![v, z] := by
    simp only [L, MultilinearMap.toLinearMap_apply]
    rw [hB]
    congr 1
    funext i
    fin_cases i <;> rfl
  have h := congrArg L ((g.orthonormalBasis x).sum_repr' q)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp only [hL] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  rfl

lemma tensorHeatOperator_covariantTensorDerivative_commutator_two
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {T : ℝ → CovariantTensorEvaluation n M 2} {t : ℝ} (ht : t ∈ interior J)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X Y : (z : M) → TangentSpace (𝓡 n) z),
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) y →
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) y →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 ![X p.2, Y p.2]) (t, y))
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    tensorHeatOperator F (fun s => (F.connection s).covariantTensorDerivative (T s)) t x ![u, v, w] -
      (F.connection t).covariantTensorDerivative (tensorHeatOperator F T t) x ![u, v, w] =
      2 * ∑ i, ∑ j, (F.connection t).curvatureTensor x u
        ((F.metric t).orthonormalBasis x i) v ((F.metric t).orthonormalBasis x j) *
        (F.connection t).covariantTensorDerivative (T t) x
          ![(F.metric t).orthonormalBasis x i, (F.metric t).orthonormalBasis x j, w] +
      2 * ∑ i, ∑ j, (F.connection t).curvatureTensor x u
        ((F.metric t).orthonormalBasis x i) w ((F.metric t).orthonormalBasis x j) *
        (F.connection t).covariantTensorDerivative (T t) x
          ![(F.metric t).orthonormalBasis x i, v, (F.metric t).orthonormalBasis x j] := by
  have hW (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => T s y z) (deriv (fun s => T s y z) t) t := by
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (z 0)
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (z 1)
    have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) (z 0)
    have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) (z 1)
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, y)) t := contMDiffAt_id.prodMk contMDiffAt_const
    have hs := ((hreg y X Y hX hY).comp t hp).contDiffAt
    have hz : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    have hc : ContDiffAt ℝ ∞ (fun s => T s y z) t := by
      convert hs using 1 <;> ext s <;> simp [X, Y, hz,
        FiberBundle.extend_apply_self]
    exact (hc.differentiableAt (by simp)).hasDerivAt
  let D := F.connection t
  let g := F.metric t
  let W : ℝ → CovariantTensorEvaluation n M 2 := fun s y z =>
    deriv (fun r => T r y z) s
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hCals := hC.tensor_calculus n M g D
  have hWs : IsSmoothCovariantTensor (W t) :=
    isSmoothCovariantTensor_timeDerivative hT hreg hW
  have hLaps : IsSmoothCovariantTensor (D.tensorLaplacian (T t)) :=
    (hCals.2.2.1 _ _ (hCals.2.2.1 _ _ (hT t))).tensorTrace
  have htime := hasDerivAt_covariantTensorDerivative_time F (W := W) ht x hT hreg hW u v w
  have htime' := htime.deriv
  have hricci := D.covariantTensorDerivative_ricciTensorAction_two hCals (hT t) x u v w
  have hlap := D.covariantTensorDerivative_tensorLaplacian_commutator_two hCals (hT t) x u v w
  have hheatder : D.covariantTensorDerivative (tensorHeatOperator F T t) x ![u, v, w] =
      D.covariantTensorDerivative (W t) x ![u, v, w] +
        D.covariantTensorDerivative (D.ricciTensorAction (T t)) x ![u, v, w] -
        D.covariantTensorDerivative (D.tensorLaplacian (T t)) x ![u, v, w] := by
    change D.covariantTensorDerivative (fun y z => W t y z +
      D.ricciTensorAction (T t) y z - D.tensorLaplacian (T t) y z) x ![u, v, w] = _
    rw [D.covariantTensorDerivative_sub
      (hWs.add (D.isSmoothCovariantTensor_ricciTensorAction_two hCals (hT t))) hLaps]
    rw [D.covariantTensorDerivative_add hWs
      (D.isSmoothCovariantTensor_ricciTensorAction_two hCals (hT t))]
  let A := fun q : TangentSpace (𝓡 n) x => deriv (fun s =>
    (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q) x) t
  have hl := tensor_slot_left_eq_sum g (hT t) x (A v u) w
  have hr := tensor_slot_right_eq_sum g (hT t) x v (A w u)
  have ha (q e : TangentSpace (𝓡 n) x) := connection_deriv_inner hC F ht x u q e
  dsimp only at ha
  dsimp only [g, A] at hl hr
  simp_rw [ha] at hl hr
  have hact : D.ricciTensorAction (D.covariantTensorDerivative (T t)) x ![u, v, w] =
      ∑ i, (D.ricci x u (g.orthonormalBasis x i) *
          D.covariantTensorDerivative (T t) x ![g.orthonormalBasis x i, v, w] +
        D.ricci x v (g.orthonormalBasis x i) *
          D.covariantTensorDerivative (T t) x ![u, g.orthonormalBasis x i, w] +
        D.ricci x w (g.orthonormalBasis x i) *
          D.covariantTensorDerivative (T t) x ![u, v, g.orthonormalBasis x i]) := by
    have h0 (e : TangentSpace (𝓡 n) x) : Function.update ![u, v, w] 0 e = ![e, v, w] := by
      ext j; fin_cases j <;> simp
    have h1 (e : TangentSpace (𝓡 n) x) : Function.update ![u, v, w] 1 e = ![u, e, w] := by
      ext j; fin_cases j <;> simp
    have h2 (e : TangentSpace (𝓡 n) x) : Function.update ![u, v, w] 2 e = ![u, v, e] := by
      ext j; fin_cases j <;> simp
    unfold ricciTensorAction
    change (∑ j : Fin 3, ∑ i, D.ricci x (![u, v, w] j) (g.orthonormalBasis x i) *
      D.covariantTensorDerivative (T t) x
        (Function.update ![u, v, w] j (g.orthonormalBasis x i))) = _
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, h0, h1, h2, Finset.sum_add_distrib, g]
    rfl
  change deriv (fun s => (F.connection s).covariantTensorDerivative (T s) x ![u, v, w]) t +
    D.ricciTensorAction (D.covariantTensorDerivative (T t)) x ![u, v, w] -
    D.tensorLaplacian (D.covariantTensorDerivative (T t)) x ![u, v, w] -
    D.covariantTensorDerivative (tensorHeatOperator F T t) x ![u, v, w] = _
  rw [htime', hheatder, hricci, hact, hl, hr]
  dsimp only at hlap
  simp only [sub_mul, neg_mul, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hlap ⊢
  dsimp only [D, g] at hlap ⊢
  linear_combination hlap

end PoincareConjecture.RicciFlow
