import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalSecondBianchi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantTensorDerivative_riemannEvaluation_eq
    (D : LeviCivitaData g) (x : M) (u a b c d : TangentSpace (𝓡 n) x) :
    let X := fun v : TangentSpace (𝓡 n) x =>
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      mvfderiv (𝓡 n) (fun y => D.curvatureTensor y (X a y) (X b y) (X c y) (X d y)) x u -
        (D.curvatureTensor x (D.connection (X a) x u) b c d +
          D.curvatureTensor x a (D.connection (X b) x u) c d +
          D.curvatureTensor x a b (D.connection (X c) x u) d +
          D.curvatureTensor x a b c (D.connection (X d) x u)) := by
  simp [covariantTensorDerivative, riemannEvaluation, Fin.sum_univ_succ, add_assoc]

lemma covariantTensorDerivative_riemannEvaluation_skew_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      -D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, d, c] := by
  have hs (y : M) (a b c d : TangentSpace (𝓡 n) y) := (hD.2.2.2.1 y a b c d).1
  rw [D.covariantTensorDerivative_riemannEvaluation_eq,
    D.covariantTensorDerivative_riemannEvaluation_eq]
  dsimp only
  let X := fun v : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hf : (fun y => D.curvatureTensor y (X a y) (X b y) (X c y) (X d y)) =
      -(fun y => D.curvatureTensor y (X a y) (X b y) (X d y) (X c y)) := by
    funext y
    exact hs y _ _ _ _
  rw [hf, mvfderiv_neg]
  change -(mvfderiv (𝓡 n) _ x u) - _ = _
  rw [hs x (D.connection (X a) x u) b c d,
    hs x a (D.connection (X b) x u) c d,
    hs x a b (D.connection (X c) x u) d,
    hs x a b c (D.connection (X d) x u)]
  ring

lemma covariantTensorDerivative_riemannEvaluation_pair_swap
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      D.covariantTensorDerivative D.riemannEvaluation x ![u, c, d, a, b] := by
  have hs (y : M) (a b c d : TangentSpace (𝓡 n) y) := (hD.2.2.2.1 y a b c d).2.1
  rw [D.covariantTensorDerivative_riemannEvaluation_eq,
    D.covariantTensorDerivative_riemannEvaluation_eq]
  dsimp only
  let X := fun v : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hf : (fun y => D.curvatureTensor y (X a y) (X b y) (X c y) (X d y)) =
      (fun y => D.curvatureTensor y (X c y) (X d y) (X a y) (X b y)) := by
    funext y
    exact hs y _ _ _ _
  rw [hf, hs x (D.connection (X a) x u) b c d,
    hs x a (D.connection (X b) x u) c d,
    hs x a b (D.connection (X c) x u) d,
    hs x a b c (D.connection (X d) x u)]
  ring

lemma covariantTensorDerivative_riemannEvaluation_skew_first
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      -D.covariantTensorDerivative D.riemannEvaluation x ![u, b, a, c, d] := by
  rw [D.covariantTensorDerivative_riemannEvaluation_pair_swap hD x u a b c d,
    D.covariantTensorDerivative_riemannEvaluation_skew_last hD x u c d a b,
    D.covariantTensorDerivative_riemannEvaluation_pair_swap hD x u c d b a]

lemma contMDiffOn_covariantDerivativeOnFields (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.covariantDerivativeOnFields X Y)) U := by
  intro y hy
  exact (D.contMDiffAt_covariantDerivativeOnFields
    (hX.contMDiffAt (hU.mem_nhds hy)) (hY.contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt

lemma covariantTensorDerivative_riemannEvaluation_eq_inner_extend
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u a b c d : TangentSpace (𝓡 n) x) :
    let X := fun v : TangentSpace (𝓡 n) x =>
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      g.inner x (D.curvatureDerivativeOnFields (X u) (X a) (X b) (X d) x) c := by
  dsimp only
  let X := fun v : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨U, hU, hx, hs⟩ := PoincareConjecture.exists_open_contMDiffOn_extend (n := n) x
  have hs' (v : TangentSpace (𝓡 n) x) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X v)) x :=
    (hs v).contMDiffAt (hU.mem_nhds hx)
  have heq (Y Z W : (y : M) → TangentSpace (𝓡 n) y)
      (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
      (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
      (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
      (y : M) (hy : y ∈ U) :
      D.curvatureOnFields Y Z W y = D.curvature y (Y y) (Z y) (W y) :=
    hD.2.2.2.2 U hU Y Z W hY hZ hW y hy
  have hC (v : TangentSpace (𝓡 n) x) :=
    D.contMDiffOn_covariantDerivativeOnFields hU (hs u) (hs v)
  have hf : (fun y => g.inner y (D.curvatureOnFields (X a) (X b) (X d) y) (X c y)) =ᶠ[𝓝 x]
      (fun y => D.curvatureTensor y (X a y) (X b y) (X c y) (X d y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [heq _ _ _ (hs a) (hs b) (hs d) y hy]
    rfl
  have hd := DFunLike.congr_fun (hf.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))) u
  change mvfderiv (𝓡 n) _ x u = mvfderiv (𝓡 n) _ x u at hd
  dsimp only [X] at hd
  have hi := D.inner_curvatureDerivativeOnFields_local (X := X u)
    (hs' a) (hs' b) (hs' c) (hs' d)
  simp only [X, FiberBundle.extend_apply_self] at hi
  rw [D.covariantTensorDerivative_riemannEvaluation_eq]
  dsimp only
  rw [hi]
  erw [hd]
  rw [
    heq _ _ _ (hC a) (hs b) (hs d) x hx,
    heq _ _ _ (hs a) (hC b) (hs d) x hx,
    heq _ _ _ (hs a) (hs b) (hs d) x hx,
    heq _ _ _ (hs a) (hs b) (hC d) x hx]
  simp only [FiberBundle.extend_apply_self, covariantDerivativeOnFields, curvatureTensor]
  ring!

end PoincareConjecture.LeviCivitaData
