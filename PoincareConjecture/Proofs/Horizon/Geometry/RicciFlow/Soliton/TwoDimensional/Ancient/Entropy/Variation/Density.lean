import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Volume








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}



theorem hasDerivAt_pullbackVolumeDensity_surface
    (F : RicciFlow 2 M J) {t : ℝ} (ht : t ∈ interior J)
    (f : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 2))
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) f x)) :
    HasDerivAt (fun s => (F.metric s).pullbackVolumeDensity f x)
      (-(F.connection t).scalarCurvature (f x) *
        (F.metric t).pullbackVolumeDensity f x) t := by
  classical
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let v := fun i => mfderiv (𝓡 2) (𝓡 2) f x (b i)
  let G := fun s => Matrix.of (fun i j => (F.metric s).inner (f x) (v i) (v j))
  let R := (F.connection t).scalarCurvature (f x)
  have hpos : 0 < (G t).det := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    exact (Matrix.posDef_gram_of_linearIndependent
      (b.toBasis.linearIndependent.map' (mfderiv (𝓡 2) (𝓡 2) f x).toLinearMap
        (LinearMap.ker_eq_bot.mpr hi))).det_pos
  have hG (i j : Fin 2) : HasDerivAt (fun s => G s i j) ((-R • G t) i j) t := by
    have h := (F.equation t (interior_subset ht) (f x) (v i) (v j)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)
    rw [(F.connection t).ricci_eq_half_scalarCurvature_mul_inner] at h
    convert h using 1 <;> first | rfl | (dsimp [G, R]; ring)
  have hd := Poincare.Matrix.hasDerivAt_sqrt_det_eq_half_trace_inv_mul G (-R • G t) t hG hpos
  have htrace : Matrix.trace ((G t)⁻¹ * (-R • G t)) = -2 * R := by
    rw [Matrix.mul_smul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.ne'), Matrix.trace_smul,
      Matrix.trace_one]
    norm_num
    ring
  rw [htrace] at hd
  change HasDerivAt (fun s => Real.sqrt (G s).det) (-R * Real.sqrt (G t).det) t
  exact hd.congr_deriv (by ring)

end PoincareConjecture.RicciFlow
