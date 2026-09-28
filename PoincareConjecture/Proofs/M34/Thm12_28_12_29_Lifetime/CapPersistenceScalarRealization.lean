import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderPullback
import PoincareConjecture.Proofs.M34.Standard.LocalHomothetyCurvature
import PoincareConjecture.Proofs.M13.Metric











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem exists_capPersistence_metric_germ (q : UnitTwoSphere) (s : ℝ)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (gE : RiemannianMetric 3 E₃) (DE : LeviCivitaData gE) (V : Set E₃),
      IsOpen V ∧ (0 : E₃) ∈ V ∧
      (∀ x ∈ V, x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
      (∀ x ∈ V, gE.euclideanCoefficients x =
        N.scale⁻¹ ^ 2 • g.pullbackCoefficients (N.capPersistenceEuclideanMap q s) x) ∧
      DE.scalarCurvature 0 = N.scale ^ 2 *
        N.connection.scalarCurvature (N.coordinate_map (q, s)) := by
  let U : Set E₃ := {x | x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    ((EuclideanSpace.proj 2 : E₃ →L[ℝ] ℝ).continuous.add continuous_const)
  have h0 : (0 : E₃) ∈ U := by simpa only [U, mem_ofPred_eq, PiLp.zero_apply, zero_add]
    using hs
  let f := N.capPersistenceEuclideanMap q s
  let B := fun x : E₃ => N.scale⁻¹ ^ 2 • g.pullbackCoefficients f x
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U := fun x hx =>
    (N.capPersistenceEuclideanMap_contMDiffAt q s hx).contMDiffWithinAt
  have hB : ContDiffOn ℝ ∞ B U := by
    let gN : RiemannianMetric 3 M := M13.scaleSmoothMetric g (N.scale⁻¹ ^ 2)
      (sq_pos_of_pos (inv_pos.mpr N.scale_pos))
    have heq : B = gN.pullbackCoefficients f := by
      funext x
      ext v w
      rfl
    rw [heq]
    intro x hx
    exact (gN.contDiffAt_pullbackCoefficients
      (N.capPersistenceEuclideanMap_contMDiffAt q s hx)).contDiffWithinAt
  have hsymm : ∀ x ∈ U, ∀ v w : E₃, B x v w = B x w v := by
    intro x _ v w
    change N.scale⁻¹ ^ 2 * g.inner _ _ _ = N.scale⁻¹ ^ 2 * g.inner _ _ _
    rw [g.symm]
  have hpos : ∀ x ∈ U, ∀ v : E₃, v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    have hc := (N.pullback_inner_comparison (z := capPersistenceSphereChart q s x) hx
      (mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) x v)).1
    rw [capPersistenceSphereChart_model] at hc
    have hp := stereographicCylinderCoefficients_pos (by norm_num : (0 : ℝ) < 2) x v hv
    apply lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hp)
    change (1 / 2 : ℝ) * stereographicCylinderCoefficients 2 x v v ≤
      N.scale⁻¹ ^ 2 * g.inner _ (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v)
    rw [N.capPersistenceEuclideanMap_mfderiv q s hx]
    exact hc
  obtain ⟨gE, DE, V, hV, h0V, hVU, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU h0 B hB hsymm hpos
  refine ⟨gE, DE, V, hV, h0V, hVU, hcoeff, ?_⟩
  have hmetric : ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 3) x,
      gE.inner x v w = N.scale⁻¹ ^ 2 *
        g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
          (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    intro x hx v w
    exact congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => A v w) (hcoeff x hx)
  have hscalar := DE.scalarCurvature_eq_of_local_homothety N.connection
    (sq_pos_of_pos (inv_pos.mpr N.scale_pos)) hV (hf.mono hVU) hmetric h0V
  have hf0 : f 0 = N.coordinate_map (q, s) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q s)
  rw [hf0] at hscalar
  simpa only [div_eq_mul_inv, inv_pow, inv_inv, mul_comm] using hscalar

end PoincareConjecture.EpsilonNeck
