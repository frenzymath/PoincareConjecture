import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private lemma contMDiffAt_one_of_metricDual (g : RiemannianMetric n M)
    {Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y
        (g.inner y (Z y))) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (T% Z) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x
  let G (y : M) := ContinuousLinearMap.inCoordinates E V (E →L[ℝ] ℝ)
    (fun y => V y →L[ℝ] ℝ) x y x y (g.inner y)
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞ G x :=
    (contMDiffAt_hom_bundle _).mp (g.contMDiff x) |>.2
  have hGinv (y : M) (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) :
      (G y).IsInvertible := by
    dsimp only [G]
    rw [ContinuousLinearMap.inCoordinates_eq hy hy']
    exact ContinuousLinearMap.isInvertible_equiv.comp
      ((g.inner_isInvertible y).comp ContinuousLinearMap.isInvertible_equiv)
  have hi := (hGinv x (FiberBundle.mem_baseSet_trivializationAt E V x)
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
      (fun y => V y →L[ℝ] ℝ) x)).contDiffAt_map_inverse (n := 1)
  have hinv := hi.contMDiffAt.comp x (hG.of_le (by simp))
  have hcoord := (contMDiffAt_totalSpace.mp hZ).2
  have hresult := hinv.clm_apply hcoord
  rw [contMDiffAt_section]
  apply hresult.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x),
    e'.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
        (fun y => V y →L[ℝ] ℝ) x)] with y hy hy'
  change (e ⟨y, Z y⟩).2 = (G y).inverse ((e' ⟨y, g.inner y (Z y)⟩).2)
  symm
  apply (hGinv y hy hy').inverse_apply_eq.mpr
  symm
  dsimp only [G]
  rw [ContinuousLinearMap.inCoordinates_eq hy hy']
  change (e'.continuousLinearEquivAt ℝ y hy')
    (g.inner y ((e.continuousLinearEquivAt ℝ y hy).symm
      ((e.continuousLinearEquivAt ℝ y hy) (Z y)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

namespace LeviCivitaData

variable {g : RiemannianMetric n M}


theorem contMDiffAt_one_gradient_of_C2 (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (T% (D.gradient f)) x := by
  apply contMDiffAt_one_of_metricDual g
  have heq (y : M) : g.inner y (D.gradient f y) = mvfderiv (𝓡 n) f y := by
    ext v
    exact D.inner_gradient f y v
  simp_rw [heq]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  convert hf.mfderiv_const (m := 1) (by norm_num) using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
    NormedSpace.fromTangentSpace]
  rfl


theorem hessian_eq_inner_connection_gradient_of_C2 (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = g.inner x (D.connection (D.gradient f) x u) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    ((D.contMDiffAt_one_gradient_of_C2 hf).mdifferentiableAt (by norm_num))
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
  change mvfderiv (𝓡 n)
    (fun y => g.inner y (D.gradient f y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x) =
      g.inner x (D.connection (D.gradient f) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x))
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) +
      g.inner x (D.gradient f x)
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x)) at h
  simp only [D.inner_gradient, FiberBundle.extend_apply_self] at h
  simpa only [hessian, hessianOnFields, FiberBundle.extend_apply_self] using
    sub_eq_iff_eq_add.mpr h


theorem mvfderiv_gradient_normSq_of_C2 (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x v =
      2 * D.hessian f x v (D.gradient f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgrad := (D.contMDiffAt_one_gradient_of_C2 hf).mdifferentiableAt (by norm_num)
  have h := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) hgrad hgrad
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) =
      g.inner x (D.connection (D.gradient f) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) (D.gradient f x) +
      g.inner x (D.gradient f x) (D.connection (D.gradient f) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) at h
  simp only [FiberBundle.extend_apply_self] at h
  rw [D.hessian_eq_inner_connection_gradient_of_C2 hf]
  rw [g.symm x (D.gradient f x)] at h
  linarith

end LeviCivitaData

namespace GradientShrinkingSolitonData

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem potential_gradient_C1 (S : GradientShrinkingSolitonData n M) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (T% (S.connection.gradient S.potential)) :=
  fun x => S.connection.contMDiffAt_one_gradient_of_C2 (S.potential_C2 x)

end GradientShrinkingSolitonData

namespace GradientShrinkingSolitonData

variable {M₂ : Type u} [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M₂] [IsManifold (𝓡 2) ∞ M₂]
  [MeasurableSpace M₂] [BorelSpace M₂] [T2Space M₂] [T3Space M₂]
  [SecondCountableTopology M₂] [ConnectedSpace M₂]


theorem connection_gradient_potential (S : GradientShrinkingSolitonData 2 M₂)
    (x : M₂) (v : TangentSpace (𝓡 2) x) :
    S.connection.connection (S.connection.gradient S.potential) x v =
      ((1 - S.connection.scalarCurvature x) / 2) • v := by
  apply (S.metric.inner_isInvertible x).injective
  ext w
  rw [← S.connection.hessian_eq_inner_connection_gradient_of_C2 (S.potential_C2 x),
    S.hessian_potential_eq_scalar]
  simp


theorem mvfderiv_potential_gradient_normSq (S : GradientShrinkingSolitonData 2 M₂)
    (x : M₂) (v : TangentSpace (𝓡 2) x) :
    mvfderiv (𝓡 2)
      (fun y => S.metric.inner y (S.connection.gradient S.potential y)
        (S.connection.gradient S.potential y)) x v =
      (1 - S.connection.scalarCurvature x) * mvfderiv (𝓡 2) S.potential x v := by
  rw [S.connection.mvfderiv_gradient_normSq_of_C2 (S.potential_C2 x),
    S.hessian_potential_eq_scalar,
    S.metric.symm x v, S.connection.inner_gradient]
  ring

end GradientShrinkingSolitonData

end PoincareConjecture
