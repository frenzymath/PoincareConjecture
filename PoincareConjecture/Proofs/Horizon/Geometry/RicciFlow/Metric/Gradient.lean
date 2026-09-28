import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Filter Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)

private theorem contMDiffAt_of_metricDual
    {Z : ℝ → (x : M) → TangentSpace (𝓡 n) x} {t : ℝ} {x : M}
    (ht : t ∈ interior J)
    (hZ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        p.2 ((F.metric p.1).inner p.2 (Z p.1 p.2))) (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Z p.1 p.2))
      (t, x) := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x
  let G (p : ℝ × M) := ContinuousLinearMap.inCoordinates E V (E →L[ℝ] ℝ)
    (fun y => V y →L[ℝ] ℝ) x p.2 x p.2 ((F.metric p.1).inner p.2)
  have hmetric := F.smooth.contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) (univ_mem : univ ∈ 𝓝 x))
  have hG : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞ G (t, x) :=
    (contMDiffAt_hom_bundle _).mp hmetric |>.2
  have hGinv (p : ℝ × M) (hy : p.2 ∈ e.baseSet) (hy' : p.2 ∈ e'.baseSet) :
      (G p).IsInvertible := by
    dsimp only [G]
    rw [ContinuousLinearMap.inCoordinates_eq hy hy']
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (((F.metric p.1).inner_isInvertible p.2).comp ContinuousLinearMap.isInvertible_equiv)
  have hi := (hGinv (t, x) (FiberBundle.mem_baseSet_trivializationAt E V x)
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x)).contDiffAt_map_inverse (n := ∞)
  have hresult := (hi.contMDiffAt.comp (t, x) hG).clm_apply
    (contMDiffAt_totalSpace.mp hZ).2
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, hresult.congr_of_eventuallyEq ?_⟩
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x)),
    hsnd.eventually (e'.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x))]
    with p hp hp'
  change (e ⟨p.2, Z p.1 p.2⟩).2 =
    (G p).inverse ((e' ⟨p.2, (F.metric p.1).inner p.2 (Z p.1 p.2)⟩).2)
  symm
  apply (hGinv p hp hp').inverse_apply_eq.mpr
  symm
  dsimp only [G]
  rw [ContinuousLinearMap.inCoordinates_eq hp hp']
  change (e'.continuousLinearEquivAt ℝ p.2 hp')
    ((F.metric p.1).inner p.2 ((e.continuousLinearEquivAt ℝ p.2 hp).symm
      ((e.continuousLinearEquivAt ℝ p.2 hp) (Z p.1 p.2)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl



theorem contMDiffAt_gradient
    {f : ℝ × M → ℝ} {t : ℝ} {x : M} (ht : t ∈ interior J)
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        ((F.connection p.1).gradient (fun y => f (p.1, y)) p.2)) (t, x) := by
  apply F.contMDiffAt_of_metricDual (x := x)
    (Z := fun s y => (F.connection s).gradient (fun z => f (s, z)) y) ht
  have heq (p : ℝ × M) : (F.metric p.1).inner p.2
      ((F.connection p.1).gradient (fun y => f (p.1, y)) p.2) =
        mvfderiv (𝓡 n) (fun y => f (p.1, y)) p.2 := by
    ext v
    exact (F.connection p.1).inner_gradient _ _ v
  simp_rw [heq]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  have hpartial : ContMDiffAt ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry (fun p : ℝ × M => fun y : M => f (p.1, y))) ((t, x), x) :=
    hf.comp ((t, x), x)
      ((contMDiffAt_fst.comp ((t, x), x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  convert hpartial.mfderiv (fun p : ℝ × M => fun y : M => f (p.1, y))
    Prod.snd contMDiffAt_snd (m := ∞) (by simp) using 1
  funext p
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
    NormedSpace.fromTangentSpace]
  rfl

theorem contMDiffAt_negative_gradient
    {f : ℝ × M → ℝ} {t : ℝ} {x : M} (ht : t ∈ interior J)
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (-((F.connection p.1).gradient (fun y => f (p.1, y)) p.2))) (t, x) := by
  have h := F.contMDiffAt_gradient ht hf
  rw [contMDiffAt_totalSpace] at h ⊢
  refine ⟨contMDiffAt_snd, h.2.neg.congr_of_eventuallyEq ?_⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) (M := M)) x
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) (M := M)) x))] with p hp
  exact (e.linear ℝ hp).map_neg _

end PoincareConjecture.RicciFlow
