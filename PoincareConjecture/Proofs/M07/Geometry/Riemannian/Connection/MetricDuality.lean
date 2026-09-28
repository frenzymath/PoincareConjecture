import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Dual








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
lemma contMDiffAt_clm_of_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    {f : M → E →L[ℝ] F} {x : M}
    (hf : ∀ v, ContMDiffAt (𝓡 n) 𝓘(ℝ, F) ∞ (fun y => f y v) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] F) ∞ f x := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp x
    (contMDiffAt_pi_space.mpr fun i => hf _)

namespace RiemannianMetric

variable {g : RiemannianMetric n M}


lemma inner_isInvertible (g : RiemannianMetric n M) (x : M) :
    (g.inner x).IsInvertible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have heq : g.inner x = (InnerProductSpace.toDual ℝ (TangentSpace (𝓡 n) x)).toContinuousLinearMap := by
    ext v w
    rfl
  rw [heq]
  exact ContinuousLinearMap.isInvertible_equiv
    (f := (InnerProductSpace.toDual ℝ (TangentSpace (𝓡 n) x)).toContinuousLinearEquiv)

lemma contMDiffAt_of_metricDual (g : RiemannianMetric n M)
    {Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y
        (g.inner y (Z y))) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x := by
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
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x)).contDiffAt_map_inverse (n := ∞)
  have hinv := hi.contMDiffAt.comp x hG
  have hcoord := (contMDiffAt_totalSpace.mp hZ).2
  have hresult := hinv.clm_apply hcoord
  rw [contMDiffAt_section]
  apply hresult.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x),
    e'.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x)] with y hy hy'
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

end RiemannianMetric

end PoincareConjecture
