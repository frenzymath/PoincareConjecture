import PoincareConjecture.Proofs.M09.CoordinateConnection
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.BilinearMap

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem coordinateConnectionCovector_apply (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w u : E) :
    coordinateConnectionCovector G z v w u = (1 / 2 : ℝ) *
      (fderiv ℝ G z (0, v) w u + fderiv ℝ G z (0, w) v u - fderiv ℝ G z (0, u) v w) := rfl

theorem coordinateConnection_add_left (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v v' w : E) :
    coordinateConnection G z (v + v') w =
      coordinateConnection G z v w + coordinateConnection G z v' w := by
  have hp : ((0, v + v') : ℝ × E) = (0, v) + (0, v') := by simp
  have hc : coordinateConnectionCovector G z (v + v') w =
      coordinateConnectionCovector G z v w + coordinateConnectionCovector G z v' w := by
    ext u
    simp only [ContinuousLinearMap.add_apply, coordinateConnectionCovector_apply,
      hp, map_add]
    ring
  simp only [coordinateConnection, hc, map_add]

theorem coordinateConnection_smul_left (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (a : ℝ) (v w : E) :
    coordinateConnection G z (a • v) w = a • coordinateConnection G z v w := by
  have hp : ((0, a • v) : ℝ × E) = a • (0, v) := by simp
  have hc : coordinateConnectionCovector G z (a • v) w =
      a • coordinateConnectionCovector G z v w := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, coordinateConnectionCovector_apply,
      hp, map_smul, smul_eq_mul]
    ring
  simp only [coordinateConnection, hc, map_smul]

theorem coordinateConnection_add_right (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w w' : E) :
    coordinateConnection G z v (w + w') =
      coordinateConnection G z v w + coordinateConnection G z v w' := by
  have hp : ((0, w + w') : ℝ × E) = (0, w) + (0, w') := by simp
  have hc : coordinateConnectionCovector G z v (w + w') =
      coordinateConnectionCovector G z v w + coordinateConnectionCovector G z v w' := by
    ext u
    simp only [ContinuousLinearMap.add_apply, coordinateConnectionCovector_apply,
      hp, map_add]
    ring
  simp only [coordinateConnection, hc, map_add]

theorem coordinateConnection_smul_right (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (a : ℝ) (v w : E) :
    coordinateConnection G z v (a • w) = a • coordinateConnection G z v w := by
  have hp : ((0, a • w) : ℝ × E) = a • (0, w) := by simp
  have hc : coordinateConnectionCovector G z v (a • w) =
      a • coordinateConnectionCovector G z v w := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, coordinateConnectionCovector_apply,
      hp, map_smul, smul_eq_mul]
    ring
  simp only [coordinateConnection, hc, map_smul]

noncomputable def coordinateConnectionBilinear (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) : E →L[ℝ] E →L[ℝ] E :=
  let L : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ (coordinateConnection G z)
    (coordinateConnection_add_left G z)
    (coordinateConnection_smul_left G z)
    (coordinateConnection_add_right G z)
    (fun a v w ↦ coordinateConnection_smul_right G z a v w)
  ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap.comp
    L).toContinuousLinearMap

theorem coordinateConnectionBilinear_apply (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (v w : E) :
    coordinateConnectionBilinear G z v w = coordinateConnection G z v w := rfl

theorem coordinateConnectionBilinear_contDiffOn (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (coordinateConnectionBilinear G) U := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  exact (coordinateConnection_smooth G U hU hG hpos).comp
    (contDiffOn_id.prodMk (contDiffOn_const (c := (v, w)))) (fun z hz ↦ hz)

end PoincareConjecture.Proofs.M09
