import PoincareConjecture.Proofs.M44.Mathlib.OpenChartDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Descent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M44

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def chartTargetLeviCivitaData
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (e : Diffeomorph (𝓡 n) (𝓡 n) U M ∞) (g : RiemannianMetric n M) :
    LeviCivitaData g := by
  let h := g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph
  let D := h.openEuclideanLeviCivitaData U
  exact g.leviCivitaDataOfCover (N := fun _ : Unit => U)
    (fun _ => h) (fun _ => D) (fun _ => e)
    (fun _ => e.contMDiff) (fun _ y => ⟨e.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (fun _ _ _ _ => rfl) (fun x => ⟨(), e.symm x, e.apply_symm_apply x⟩)

noncomputable def physicalBufferFlow {J : Set ℝ} (F : RicciFlow n M J)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞) :
    RicciFlow n (⟨e.target, e.open_target⟩ : Opens M) J :=
  F.pullbackWithConnection Subtype.val
    (open_inclusion_isLocalDiffeomorph (⟨e.target, e.open_target⟩ : Opens M))
    (fun t => chartTargetLeviCivitaData (⟨e.source, e.open_source⟩ :
      Opens (EuclideanSpace ℝ (Fin n))) (sourceTargetDiffeomorph e)
        ((F.metric t).pullbackOfLocalDiffeomorph Subtype.val
          (open_inclusion_isLocalDiffeomorph (⟨e.target, e.open_target⟩ : Opens M))))

theorem physicalBufferFlow_metric_inner {J : Set ℝ} (F : RicciFlow n M J)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (t : ℝ) (x : (⟨e.target, e.open_target⟩ : Opens M))
    (v w : TangentSpace (𝓡 n) x) :
    ((physicalBufferFlow F e).metric t).inner x v w =
      (F.metric t).inner x.1
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x v)
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x w) := rfl

theorem physicalBufferFlow_curvatureDerivativeNorm {J : Set ℝ} (F : RicciFlow n M J)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (t : ℝ) (m : ℕ) (x : (⟨e.target, e.open_target⟩ : Opens M)) :
    ((physicalBufferFlow F e).connection t).curvatureDerivativeNorm m x =
      (F.connection t).curvatureDerivativeNorm m x.1 := by
  let hi := open_inclusion_isLocalDiffeomorph (I := 𝓡 n)
    (⟨e.target, e.open_target⟩ : Opens M)
  exact ((physicalBufferFlow F e).connection t).curvatureDerivativeNorm_eq_pullback
    (F.connection t) isOpen_univ hi.contMDiff.contMDiffOn
    (fun y _ => ⟨hi.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (fun _ _ _ _ => rfl) m (mem_univ x)

end PoincareConjecture.M44
