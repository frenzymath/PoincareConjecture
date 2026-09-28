import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution.ConnectionTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Jets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem hasDerivAt_mvfderiv_time_local
    {f : ℝ × M → ℝ} {df : M → ℝ} {t : ℝ} {x : M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (hdf : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => f (s, y)) (df y) t)
    (v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => mvfderiv (𝓡 n) (fun y => f (s, y)) x v)
      (mvfderiv (𝓡 n) df x v) t := by
  classical
  let U := {y | HasDerivAt (fun s => f (s, y)) (df y) t}
  let f' : ℝ × M → ℝ := fun p => if p.2 ∈ U then f p else 0
  let df' : M → ℝ := fun y => if y ∈ U then df y else 0
  have hU : U ∈ 𝓝 x := hdf
  have hf' : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f' (t, x) := by
    apply hf.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.tendsto.eventually hU] with p hp
    exact if_pos hp
  have hdf' (y : M) : HasDerivAt (fun s => f' (s, y)) (df' y) t := by
    by_cases hy : y ∈ U
    · simpa only [f', df', if_pos hy] using
        (show HasDerivAt (fun s => f (s, y)) (df y) t from hy)
    · simpa only [f', df', if_neg hy] using hasDerivAt_const t (0 : ℝ)
  have h := Poincare.Manifold.hasDerivAt_mvfderiv_time hf' hdf' v
  have hs (s : ℝ) : (fun y => f' (s, y)) =ᶠ[𝓝 x] fun y => f (s, y) := by
    filter_upwards [hU] with y hy
    exact if_pos hy
  have hd : df' =ᶠ[𝓝 x] df := by
    filter_upwards [hU] with y hy
    exact if_pos hy
  have hs' (s : ℝ) : mvfderiv (𝓡 n) (fun y => f' (s, y)) x v =
      mvfderiv (𝓡 n) (fun y => f (s, y)) x v := by
    exact DFunLike.congr_fun ((hs s).mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))) v
  have hd' : mvfderiv (𝓡 n) df' x v = mvfderiv (𝓡 n) df x v := by
    exact DFunLike.congr_fun (hd.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))) v
  simpa only [hs', hd'] using h

private theorem deriv_connection_eq_extend
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    deriv (fun s => (F.connection s).connection Y x) t =
      deriv (fun s => (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x)) x) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x)
  have hZ := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) (Y x)
  have heq (s : ℝ) :
      (F.connection s).connection Y x - (F.connection t).connection Y x =
        (F.connection s).connection Z x - (F.connection t).connection Z x := by
    have h1 := (F.connection s).connection.isCovariantDerivativeOnUniv.difference_apply
      (F.connection t).connection.isCovariantDerivativeOnUniv (by simp)
      (hY.mdifferentiableAt (by simp))
    have h2 := (F.connection s).connection.isCovariantDerivativeOnUniv.difference_apply
      (F.connection t).connection.isCovariantDerivativeOnUniv (by simp)
      (hZ.mdifferentiableAt (by simp))
    simp only [FiberBundle.extend_apply_self] at h2
    exact h1.symm.trans h2
  have h1 := ((F.contDiffAt_connection ht hY).differentiableAt (by simp)).hasDerivAt.sub_const
    ((F.connection t).connection Y x)
  have h2 := ((F.contDiffAt_connection ht hZ).differentiableAt (by simp)).hasDerivAt.sub_const
    ((F.connection t).connection Z x)
  exact h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall heq))

private theorem hasDerivAt_inner_connection
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x)
    (u w : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => (F.metric s).inner x ((F.connection s).connection Y x u) w)
      (-2 * (F.connection t).ricci x ((F.connection t).connection Y x u) w +
        (F.connection t).ricciConnectionVariation x ![u, Y x, w]) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  have ha := (F.contDiffAt_inner ht x).differentiableAt (by simp) |>.hasDerivAt
  have hb := (F.contDiffAt_connection ht hY).differentiableAt (by simp) |>.hasDerivAt
  have hbu := hb.clm_apply (hasDerivAt_const t u)
  have h := (ha.clm_apply hbu).clm_apply (hasDerivAt_const t w)
  have hc := (ha.clm_apply (hasDerivAt_const t ((F.connection t).connection Y x u))).clm_apply
    (hasDerivAt_const t w)
  have heq := hc.unique ((F.equation t (interior_subset ht) x
    ((F.connection t).connection Y x u) w).hasDerivAt (mem_interior_iff_mem_nhds.mp ht))
  simp only [map_zero, add_zero, add_apply] at h heq
  apply h.congr_deriv
  rw [heq, deriv_connection_eq_extend F ht hY,
    F.inner_deriv_connection_extend_of_equation ht]
  rfl

private theorem mvfderiv_tensor_normal {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hY : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (Y i)) x)
    (u : TangentSpace (𝓡 n) x) (hz : ∀ i, D.connection (Y i) x u = 0) :
    mvfderiv (𝓡 n) (fun y => T y (fun i => Y i y)) x u =
      D.covariantTensorDerivative T x (Fin.cons u (fun i => Y i x)) := by
  rw [D.covariantTensorDerivative_on_fields hT Y x hY]
  obtain ⟨A, hA⟩ := hT.1 x
  simp only [hz, hA, A.map_update_zero, Finset.sum_const_zero, sub_zero]

private theorem mvfderiv_ricci_vanishing {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {x : M} {V W : (y : M) → TangentSpace (𝓡 n) y}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) x)
    (hzero : V x = 0) (u : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => D.ricci y (V y) (W y)) x u =
      D.ricci x (D.connection V x u) (W x) := by
  have hR := D.ricciEvaluation_isSmooth_manifold
  have hDR := D.covariantTensorDerivative_isSmooth hR
  have h := D.covariantTensorDerivative_on_fields hR ![V, W] x
    (by intro i; fin_cases i; exact hV.mdifferentiableAt (by simp); exact hW.mdifferentiableAt (by simp)) u
  have hvec (y : M) : (fun i : Fin 2 => ![V, W] i y) = ![V y, W y] := by
    ext i; fin_cases i <;> rfl
  simp_rw [hvec] at h
  simp only [Matrix.Fin.cons_vecCons] at h
  obtain ⟨A, hA⟩ := hR.1 x
  obtain ⟨B, hB⟩ := hDR.1 x
  have hz1 (w : TangentSpace (𝓡 n) x) : D.ricci x (V x) w = 0 := by
    change D.ricciEvaluation x ![V x, w] = 0
    rw [hA]
    exact A.map_coord_zero 0 hzero
  have hz2 : D.covariantTensorDerivative D.ricciEvaluation x ![u, V x, W x] = 0 := by
    rw [hB]
    exact B.map_coord_zero 1 hzero
  rw [hz2] at h
  simp only [Fin.sum_univ_two] at h
  simp only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h
  rw [hz1] at h
  linarith

private theorem hasDerivAt_directional_inner_connection_normal
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    {Y Z W : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) U)
    (hYn : ∀ a, (F.connection t).connection Y x a = 0)
    (hZn : ∀ a, (F.connection t).connection Z x a = 0)
    (hWn : ∀ a, (F.connection t).connection W x a = 0)
    (u : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    HasDerivAt (fun s => mvfderiv (𝓡 n)
      (fun y => (F.metric s).inner y ((F.connection s).connection Z y (Y y)) (W y)) x u)
      (-2 * D.ricci x (D.connection (D.covariantDerivativeOnFields Y Z) x u) (W x) +
        D.covariantTensorDerivative D.ricciConnectionVariation x ![u, Y x, Z x, W x]) t := by
  let D := F.connection t
  have hYx := hY.contMDiffAt (hU.mem_nhds hx)
  have hZx := hZ.contMDiffAt (hU.mem_nhds hx)
  have hWx := hW.contMDiffAt (hU.mem_nhds hx)
  let V := D.covariantDerivativeOnFields Y Z
  have hV := D.contMDiffAt_covariantDerivativeOnFields hYx hZx
  have hR := D.ricciEvaluation_isSmooth_manifold.contMDiffAt_apply
    (X := ![V, W]) (by intro i; fin_cases i; exact hV; exact hWx)
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => D.ricci y (V y) (W y)) x at hR
  have hS := D.ricciConnectionVariation_isSmooth.contMDiffAt_apply
    (X := ![Y, Z, W]) (by intro i; fin_cases i; exact hYx; exact hZx; exact hWx)
  have hvec (y : M) : (fun i : Fin 3 => ![Y, Z, W] i y) = ![Y y, Z y, W y] := by
    ext i; fin_cases i <;> rfl
  simp_rw [hvec] at hS
  have h := hasDerivAt_mvfderiv_time_local
    (F.contMDiffAt_inner_connection_fields ht hYx hZx hWx)
    (df := fun y => -2 * D.ricci y (V y) (W y) +
      D.ricciConnectionVariation y ![Y y, Z y, W y]) ?_ u
  · apply h.congr_deriv
    have hdR := mvfderiv_ricci_vanishing D hV hWx (hZn (Y x)) u
    have hdS := mvfderiv_tensor_normal D D.ricciConnectionVariation_isSmooth
      ![Y, Z, W] x
      (by intro i; fin_cases i; exact hYx.mdifferentiableAt (by simp)
          exact hZx.mdifferentiableAt (by simp); exact hWx.mdifferentiableAt (by simp)) u
      (by intro i; fin_cases i; exact hYn u; exact hZn u; exact hWn u)
    have hadd := mvfderiv_fun_add
      ((mdifferentiableAt_const (c := (-2 : ℝ))).mul (hR.mdifferentiableAt (by simp)))
      (hS.mdifferentiableAt (by simp))
    simp only [Pi.mul_apply] at hadd
    rw [hadd, mvfderiv_mul (mdifferentiableAt_const (c := (-2 : ℝ)))
      (hR.mdifferentiableAt (by simp))]
    simp only [mvfderiv_const, smul_zero, add_zero, add_apply, smul_apply, smul_eq_mul]
    change -2 * mvfderiv (𝓡 n) (fun y => D.ricci y (V y) (W y)) x u +
      mvfderiv (𝓡 n) (fun y => D.ricciConnectionVariation y ![Y y, Z y, W y]) x u = _
    rw [hdR]
    have hdS' : mvfderiv (𝓡 n)
        (fun y => D.ricciConnectionVariation y ![Y y, Z y, W y]) x u =
        D.covariantTensorDerivative D.ricciConnectionVariation x ![u, Y x, Z x, W x] := by
      simpa only [hvec, Matrix.Fin.cons_vecCons] using hdS
    rw [hdS']
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hasDerivAt_inner_connection F ht (hZ.contMDiffAt (hU.mem_nhds hy)) (Y y) (W y)

private theorem curvature_inner_eq_derivatives {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {x : M} {X Y Z W : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) x) :
    g.inner x (D.curvatureOnFields X Y Z x) (W x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (D.connection Z y (Y y)) (W y)) x (X x) -
        mvfderiv (𝓡 n) (fun y => g.inner y (D.connection Z y (X y)) (W y)) x (Y x) -
        g.inner x (D.connection Z x (Y x)) (D.connection W x (X x)) +
        g.inner x (D.connection Z x (X x)) (D.connection W x (Y x)) -
        g.inner x (D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x)) (W x) := by
  have h1 := D.horizon_mvfderiv_inner X
    ((D.contMDiffAt_covariantDerivativeOnFields hY hZ).mdifferentiableAt (by simp))
    (hW.mdifferentiableAt (by simp))
  have h2 := D.horizon_mvfderiv_inner Y
    ((D.contMDiffAt_covariantDerivativeOnFields hX hZ).mdifferentiableAt (by simp))
    (hW.mdifferentiableAt (by simp))
  dsimp only [LeviCivitaData.covariantDerivativeOnFields] at h1 h2
  rw [h1, h2]
  simp only [LeviCivitaData.curvatureOnFields, map_sub, sub_apply]
  unfold LeviCivitaData.covariantDerivativeOnFields
  ring

private theorem hasDerivAt_inner_normal_connections
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y Z : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) x)
    (u v : TangentSpace (𝓡 n) x)
    (hYu : (F.connection t).connection Y x u = 0)
    (hZv : (F.connection t).connection Z x v = 0) :
    HasDerivAt (fun s => (F.metric s).inner x
      ((F.connection s).connection Y x u) ((F.connection s).connection Z x v)) 0 t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  have hM := (F.contDiffAt_inner ht x).differentiableAt (by simp) |>.hasDerivAt
  have hA := ((F.contDiffAt_connection ht hY).differentiableAt (by simp)).hasDerivAt.clm_apply
    (hasDerivAt_const t u)
  have hB := ((F.contDiffAt_connection ht hZ).differentiableAt (by simp)).hasDerivAt.clm_apply
    (hasDerivAt_const t v)
  have h := (hM.clm_apply hA).clm_apply hB
  simpa only [hYu, hZv, map_zero, zero_apply, add_zero] using h

private theorem hasDerivAt_curvature_normal_fields
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    {X Y Z W : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) U)
    (hXn : ∀ a, (F.connection t).connection X x a = 0)
    (hYn : ∀ a, (F.connection t).connection Y x a = 0)
    (hZn : ∀ a, (F.connection t).connection Z x a = 0)
    (hWn : ∀ a, (F.connection t).connection W x a = 0) :
    let D := F.connection t
    HasDerivAt (fun s => (F.metric s).inner x
      ((F.connection s).curvatureOnFields X Y Z x) (W x))
      (-2 * D.ricci x (D.curvature x (X x) (Y x) (Z x)) (W x) +
        D.covariantTensorDerivative D.ricciConnectionVariation x ![X x, Y x, Z x, W x] -
        D.covariantTensorDerivative D.ricciConnectionVariation x ![Y x, X x, Z x, W x]) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  have hXx := hX.contMDiffAt (hU.mem_nhds hx)
  have hYx := hY.contMDiffAt (hU.mem_nhds hx)
  have hZx := hZ.contMDiffAt (hU.mem_nhds hx)
  have hWx := hW.contMDiffAt (hU.mem_nhds hx)
  have hbr : VectorField.mlieBracket (𝓡 n) X Y x = 0 := by
    rw [← D.covariantDerivativeOnFields_sub_swap
      (hXx.mdifferentiableAt (by simp)) (hYx.mdifferentiableAt (by simp))]
    simp only [LeviCivitaData.covariantDerivativeOnFields, hXn, hYn, sub_self, D]
  have hd1 := hasDerivAt_directional_inner_connection_normal F ht hU hx
    hY hZ hW hYn hZn hWn (X x)
  have hd2 := hasDerivAt_directional_inner_connection_normal F ht hU hx
    hX hZ hW hXn hZn hWn (Y x)
  have hz1 := hasDerivAt_inner_normal_connections F ht hZx hWx (Y x) (X x)
    (hZn (Y x)) (hWn (X x))
  have hz2 := hasDerivAt_inner_normal_connections F ht hZx hWx (X x) (Y x)
    (hZn (X x)) (hWn (Y x))
  have h := ((hd1.sub hd2).sub hz1).add hz2
  have heq (s : ℝ) := curvature_inner_eq_derivatives (F.connection s) hXx hYx hZx hWx
  simp only [hbr, map_zero, zero_apply, sub_zero] at heq
  have h' := h.congr_of_eventuallyEq (Eventually.of_forall heq)
  apply h'.congr_deriv
  have hc : D.curvature x (X x) (Y x) (Z x) =
      D.connection (D.covariantDerivativeOnFields Y Z) x (X x) -
        D.connection (D.covariantDerivativeOnFields X Z) x (Y x) := by
    rw [← D.curvatureOnFields_eq_curvature_manifold hXx hYx hZx]
    simp only [LeviCivitaData.curvatureOnFields, hbr, map_zero, sub_zero]
    rfl
  obtain ⟨A, hA⟩ := D.ricciEvaluation_isSmooth_manifold.1 x
  let B := bilinearOfTwoTensor A
  have hB (a b : TangentSpace (𝓡 n) x) : D.ricci x a b = B a b := hA ![a, b]
  change _ = -2 * D.ricci x (D.curvature x (X x) (Y x) (Z x)) (W x) + _ - _
  rw [hc]
  dsimp only [D] at hB ⊢
  simp only [hB, map_sub, LinearMap.sub_apply]
  ring

private theorem exists_normal_field {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x) :
    ∃ Y : (y : M) → TangentSpace (𝓡 n) y, Y x = v ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) (extChartAt (𝓡 n) x).source ∧
      ∀ a, D.connection Y x a = 0 := by
  obtain ⟨r, Y, _, _, hY, hYx, _, hn, _⟩ := D.exists_radialParallelField x v
  refine ⟨LeviCivitaData.fieldFromCenteredCoordinates x Y, hYx, ?_, hn⟩
  intro y hy
  exact (LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates x hY.contDiffAt hy).contMDiffWithinAt

theorem hasDerivAt_curvatureTensor_connectionVariation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    HasDerivAt (fun s => (F.connection s).curvatureTensor x u v w z)
      (-2 * D.ricci x (D.curvature x u v z) w +
        D.covariantTensorDerivative D.ricciConnectionVariation x ![u, v, z, w] -
        D.covariantTensorDerivative D.ricciConnectionVariation x ![v, u, z, w]) t := by
  obtain ⟨X, hXu, hX, hXn⟩ := exists_normal_field (F.connection t) x u
  obtain ⟨Y, hYv, hY, hYn⟩ := exists_normal_field (F.connection t) x v
  obtain ⟨Z, hZz, hZ, hZn⟩ := exists_normal_field (F.connection t) x z
  obtain ⟨W, hWw, hW, hWn⟩ := exists_normal_field (F.connection t) x w
  have hx := mem_extChartAt_source (I := 𝓡 n) x
  have hU := isOpen_extChartAt_source (I := 𝓡 n) x
  have h := hasDerivAt_curvature_normal_fields F ht hU hx hX hY hZ hW hXn hYn hZn hWn
  have heq (s : ℝ) := (F.connection s).curvatureOnFields_eq_curvature_manifold
    (hX.contMDiffAt (hU.mem_nhds hx)) (hY.contMDiffAt (hU.mem_nhds hx))
    (hZ.contMDiffAt (hU.mem_nhds hx))
  simp only [heq, hXu, hYv, hZz, hWw] at h
  exact h

end PoincareConjecture.RicciFlow
