import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.LocalCalculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma ricci_symm_of_equation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    (F.connection t).ricci x a b = (F.connection t).ricci x b a := by
  have hi (u v : TangentSpace (𝓡 n) x) :=
    (F.equation t (interior_subset ht) x u v).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)
  have h := (hi a b).unique (by simpa only [(F.metric _).symm] using hi b a)
  linarith

private lemma ricci_sub_left_of_equation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    (F.connection t).ricci x (a - b) c =
      (F.connection t).ricci x a c - (F.connection t).ricci x b c := by
  have hi (u v : TangentSpace (𝓡 n) x) :=
    (F.equation t (interior_subset ht) x u v).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)
  have h := (hi (a - b) c).unique (((hi a c).sub (hi b c)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by simp only [map_sub, sub_apply, Pi.sub_apply]))
  linarith

private lemma ricci_contMDiffAt_fields
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (F.connection t).ricci y (Y y) (Z y)) x := by
  exact (F.contMDiffAt_ricci_fields ht hY hZ).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)

lemma metric_directional_hasDerivAt_of_equation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {x : M}
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => mvfderiv (𝓡 n)
      (fun y => (F.metric s).inner y (Y y) (Z y)) x v)
      (-2 * mvfderiv (𝓡 n) (fun y => (F.connection t).ricci y (Y y) (Z y)) x v) t := by
  have hR := (ricci_contMDiffAt_fields F ht hY hZ).mdifferentiableAt (by simp)
  have h := Poincare.Manifold.hasDerivAt_mvfderiv_time
    (F.contMDiffAt_inner_fields ht hY hZ)
    (fun y => (F.equation t (interior_subset ht) y (Y y) (Z y)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)) v
  apply h.congr_deriv
  rw [mvfderiv_fun_mul mdifferentiableAt_const hR]
  simp [mvfderiv]

lemma metric_directional_hasDerivAt
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus) {x : M}
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => mvfderiv (𝓡 n)
      (fun y => (F.metric s).inner y (Y y) (Z y)) x v)
      (-2 * mvfderiv (𝓡 n) (fun y => (F.connection t).ricci y (Y y) (Z y)) x v) t := by
  have _ := hD
  exact F.metric_directional_hasDerivAt_of_equation ht hY hZ v

private lemma metric_connection_hasDerivAt
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (u w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt (fun s => (F.metric s).inner x ((F.connection s).connection Y x u) w)
      (-2 * (F.connection t).ricci x ((F.connection t).connection Y x u) w +
        (F.metric t).inner x ((deriv (fun s => (F.connection s).connection Y x) t) u) w) t := by
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
  exact h.congr_deriv (by rw [heq])

private lemma connection_timeDerivative_koszul
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {x : M}
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    (F.metric t).inner x ((deriv (fun s => (F.connection s).connection Y x) t) (X x)) (Z x) =
      -mvfderiv (𝓡 n) (fun y => (F.connection t).ricci y (Y y) (Z y)) x (X x) -
      mvfderiv (𝓡 n) (fun y => (F.connection t).ricci y (Z y) (X y)) x (Y x) +
      mvfderiv (𝓡 n) (fun y => (F.connection t).ricci y (X y) (Y y)) x (Z x) -
      (F.connection t).ricci x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) +
      (F.connection t).ricci x (VectorField.mlieBracket (𝓡 n) Y Z x) (X x) -
      (F.connection t).ricci x (VectorField.mlieBracket (𝓡 n) Z X x) (Y x) +
      2 * (F.connection t).ricci x ((F.connection t).connection Y x (X x)) (Z x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hi (a b : TangentSpace (𝓡 n) x) :=
    (F.equation t (interior_subset ht) x a b).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
  have h := (((((metric_directional_hasDerivAt_of_equation F ht hY hZ (X x)).add
    (metric_directional_hasDerivAt_of_equation F ht hZ hX (Y x))).sub
    (metric_directional_hasDerivAt_of_equation F ht hX hY (Z x))).add
    (hi (VectorField.mlieBracket (𝓡 n) X Y x) (Z x))).sub
    (hi (VectorField.mlieBracket (𝓡 n) Y Z x) (X x))).add
    (hi (VectorField.mlieBracket (𝓡 n) Z X x) (Y x))
  have heq : (fun s => 2 * (F.metric s).inner x ((F.connection s).connection Y x (X x)) (Z x))
      =ᶠ[𝓝 t] (fun s =>
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (Y y) (Z y)) x (X x) +
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (Z y) (X y)) x (Y x) -
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (X y) (Y y)) x (Z x) +
        (F.metric s).inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
        (F.metric s).inner x (VectorField.mlieBracket (𝓡 n) Y Z x) (X x) +
        (F.metric s).inner x (VectorField.mlieBracket (𝓡 n) Z X x) (Y x)) :=
    Filter.Eventually.of_forall fun s => (F.connection s).koszul_identity
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
  have hl := (metric_connection_hasDerivAt F ht hY (X x) (Z x)).const_mul 2
  have he := hl.unique (h.congr_of_eventuallyEq heq)
  linarith




theorem inner_deriv_connection_extend_of_equation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    (F.metric t).inner x
        ((deriv (fun s => (F.connection s).connection
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t) u) w =
      -(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![u, v, w] -
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![v, u, w] +
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![w, u, v] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) u
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) v
  have hZ := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) w
  have hs (y : M) (a b : TangentSpace (𝓡 n) y) :
      (F.connection t).ricci y a b = (F.connection t).ricci y b a :=
    ricci_symm_of_equation F ht y a b
  have hsub (a b c : TangentSpace (𝓡 n) x) :
      (F.connection t).ricci x (a - b) c =
        (F.connection t).ricci x a c - (F.connection t).ricci x b c :=
    ricci_sub_left_of_equation F ht x a b c
  have h := connection_timeDerivative_koszul F ht hX hY hZ
  rw [← (F.connection t).covariantDerivativeOnFields_sub_swap
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp)),
    ← (F.connection t).covariantDerivativeOnFields_sub_swap
      (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp)),
    ← (F.connection t).covariantDerivativeOnFields_sub_swap
      (hZ.mdifferentiableAt (by simp)) (hX.mdifferentiableAt (by simp))] at h
  simp only [LeviCivitaData.covariantDerivativeOnFields, FiberBundle.extend_apply_self,
    hsub] at h
  simp only [LeviCivitaData.covariantTensorDerivative, LeviCivitaData.ricciEvaluation,
    Fin.sum_univ_two]
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [h]
  simp only [hs x _ ((F.connection t).connection _ x _)]
  have he : (fun y => (F.connection t).ricci y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u y)) =
      (fun y => (F.connection t).ricci y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y)) := funext fun y => hs y _ _
  rw [he]
  ring


theorem inner_deriv_connection_extend
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    (F.metric t).inner x
        ((deriv (fun s => (F.connection s).connection
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t) u) w =
      -(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![u, v, w] -
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![v, u, w] +
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![w, u, v] := by
  have _ := hD
  exact F.inner_deriv_connection_extend_of_equation ht x u v w


theorem connection_hasDerivAt_ricci_of_equation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∃ A : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      HasDerivAt (fun s => (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) A t ∧
      ∀ u w : TangentSpace (𝓡 n) x,
        (F.metric t).inner x (A u) w =
          -(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![u, v, w] -
            (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![v, u, w] +
            (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![w, u, v] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  refine ⟨_, (F.contDiffAt_connection ht
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)).differentiableAt
      (by simp) |>.hasDerivAt, ?_⟩
  intro u w
  exact F.inner_deriv_connection_extend_of_equation ht x u v w


theorem connection_hasDerivAt_ricci
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∃ A : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      HasDerivAt (fun s => (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) A t ∧
      ∀ u w : TangentSpace (𝓡 n) x,
        (F.metric t).inner x (A u) w =
          -(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![u, v, w] -
            (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![v, u, w] +
            (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![w, u, v] := by
  have _ := hD
  exact F.connection_hasDerivAt_ricci_of_equation ht x v

end PoincareConjecture.RicciFlow
