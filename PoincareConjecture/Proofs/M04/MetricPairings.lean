import PoincareConjecture.Proofs.M04.FixedExtension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Function Topology Filter

universe u v w

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffAt_clm_of_apply
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : M → E →L[ℝ] F} {x : M}
    (hL : ∀ v : E, ContMDiffAt (𝓡 n) 𝓘(ℝ, F) ∞ (fun y ↦ L y v) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] F) ∞ L x := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have hcoord : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin d → F) ∞ (fun y ↦ e₂ (L y)) x := by
    apply contMDiffAt_pi_space.mpr
    intro i
    exact hL _
  have h := e₂.symm.toContinuousLinearMap.contMDiffAt.comp x hcoord
  have heq : (fun y ↦ e₂.symm (e₂ (L y))) = L := by
    funext y
    exact e₂.symm_apply_apply (L y)
  have h' : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] F) ∞
      (fun y ↦ e₂.symm (e₂ (L y))) x := by
    simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! h
  rw [heq] at h'
  exact h'

theorem contMDiffAt_section_of_metric_pairings (g : RiemannianMetric n M)
    (σ : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hσ : ∀ v : TangentSpace (𝓡 n) x,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y ↦ g.inner y (σ y)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% σ) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let t := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let S := fun y ↦ t.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ t.baseSet) :
      FiberBundle.extend E (S x v) y = S y v := by
    change t.symm y (t ⟨x, t.symmL ℝ x v⟩).2 = t.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hx,
      t.continuousLinearMapAt_symmL hx, t.symmL_apply hy]
  have hS (v : E) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (T% (fun y ↦ S y v)) x := by
    have he := (contMDiffOn_extend_baseSet (S x v)).contMDiffAt (t.open_baseSet.mem_nhds hx)
    apply he.congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy).symm
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    (g.inner y).bilinearComp (S y) (S y)
  let P : M → E →L[ℝ] ℝ := fun y ↦ (g.inner y (σ y)).comp (S y)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : M → E →L[ℝ] E := fun y ↦ Q.toContinuousLinearMap.comp (B y)
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    exact (hS v).inner_bundle (hS w)
  have hP : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] ℝ) ∞ P x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply (hσ (S x v)).congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    exact congrArg (g.inner y (σ y)) (hSext v hy).symm
  have hA : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ A x :=
    contMDiffAt_const.clm_comp hB
  have hInv {y : M} (hy : y ∈ t.baseSet) : (A y).IsInvertible := by
    have hz (v : E) (hv : A y v = 0) : v = 0 := by
      have hBv : B y v = 0 := Q.injective (by simpa [A] using hv)
      have hinner : g.inner y (S y v) (S y v) = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hBv
      have hSv : S y v = 0 := by
        by_contra hne
        exact (ne_of_gt (g.pos y _ hne)) hinner
      have hv' := congrArg (t.continuousLinearMapAt ℝ y) hSv
      simpa only [S, t.continuousLinearMapAt_symmL hy, map_zero] using hv'
    have hinj : Function.Injective (A y) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (A y) :=
      (LinearMap.injective_iff_surjective).mp hinj
    exact ⟨(LinearEquiv.ofBijective (A y).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  have hAi : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ (A y).inverse) x :=
    (hInv hx).contDiffAt_map_inverse.contMDiffAt.comp x hA
  have hrec : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
      (fun y ↦ (A y).inverse (Q (P y))) x :=
    hAi.clm_apply (Q.toContinuousLinearMap.contMDiffAt.comp x hP)
  rw [t.contMDiffAt_section_iff hx]
  apply hrec.congr_of_eventuallyEq
  filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hy]
  apply Eq.symm
  apply (hInv hy).inverse_apply_eq.mpr
  change Q (P y) = Q (B y (t.continuousLinearMapAt ℝ y (σ y)))
  apply congrArg Q
  ext v
  change g.inner y (σ y) (S y v) =
    g.inner y (S y (t.continuousLinearMapAt ℝ y (σ y))) (S y v)
  rw [t.symmL_continuousLinearMapAt hy]

end PoincareConjecture.M04
