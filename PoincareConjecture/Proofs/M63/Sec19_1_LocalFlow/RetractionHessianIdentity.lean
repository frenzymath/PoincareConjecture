import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddingHessianVector
import PoincareConjecture.Proofs.M63.Mathlib.FixedCompositionSecondDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ ι

theorem coordinateHessian_retraction_identity {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {r : W → W}
    (hr : ContDiffOn ℝ 2 r U) (hre : ∀ p, r (e p) = e p)
    (p : M) (v w : TangentSpace (𝓡 n) p) :
    fderiv ℝ (fderiv ℝ r) (e p)
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e p v) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p w) +
      fderiv ℝ r (e p) (coordinateHessian D e p v w) = coordinateHessian D e p v w := by
  let c := chartAt E p
  let f : E → W := e ∘ c.symm
  let v0 := mfderiv (𝓡 n) (𝓡 n) c p v
  let w0 := mfderiv (𝓡 n) (𝓡 n) c p w
  have hp : p ∈ c.source := mem_chart_source E p
  have hy : c p ∈ c.target := c.map_source hp
  have hf : ContDiffOn ℝ ∞ f c.target :=
    (he.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn
  have hfc : f (c p) = e p := congrArg e (c.left_inv hp)
  have hv : chartVectorField p v0 p = v := chartVectorField_differential p p v hp
  have hw : chartVectorField p w0 p = w := chartVectorField_differential p p w hp
  have hdf : fderiv ℝ f (c p) =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c.symm (c p))).comp
        (mfderiv (𝓡 n) (𝓡 n) c.symm (c p)) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp (c p) (he.mdifferentiable (by simp)).mdifferentiableAt
      ((mdifferentiable_chart (I := 𝓡 n) p).symm.mdifferentiableAt hy)
  have hd (u : E) : fderiv ℝ f (c p) u =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e p (chartVectorField p u p) := by
    have h := congrArg (fun L : E →L[ℝ] W => L u) hdf
    change fderiv ℝ f (c p) u = mfderiv (𝓡 n) 𝓘(ℝ, W) e (c.symm (c p))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c p) u) at h
    erw [← chartVectorField_at_inverse p u (c p) hy, c.left_inv hp] at h
    exact h
  have hH : coordinateHessian D e p v w =
      fderiv ℝ (fderiv ℝ f) (c p) v0 w0 -
        fderiv ℝ f (c p)
          (coordinateChristoffel (g.pullbackCoefficients c.symm) (c p) v0 w0) := by
    have h := coordinateHessian_eq_chart D he p p hp v0 w0
    dsimp only at h
    rw [hv, hw] at h
    exact h
  have h := (fixedComposition_second_derivative c.open_target hU
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hr
    (fun y _ => heU (mem_range_self (c.symm y))) (fun y _ => hre (c.symm y)) hy).2
      v0 w0 (coordinateChristoffel (g.pullbackCoefficients c.symm) (c p) v0 w0)
  rw [← hH, hfc, hd v0, hd w0, hv, hw] at h
  exact h

end PoincareConjecture.M63
