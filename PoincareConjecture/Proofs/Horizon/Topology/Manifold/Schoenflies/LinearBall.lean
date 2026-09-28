import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.LinearBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]


def denominator (A : E ≃L[Real] E) (x : E) : Real :=
  1 + ‖A x‖ ^ 2 - ‖x‖ ^ 2


def map (A : E ≃L[Real] E) (x : E) : E :=
  (Real.sqrt (denominator A x))⁻¹ • A x

theorem contDiff_denominator (A : E ≃L[Real] E) :
    ContDiff Real ∞ (denominator A) :=
  (contDiff_const.add (A.contDiff.norm_sq (𝕜 := Real))).sub (contDiff_norm_sq Real)

theorem contDiffOn_map (A : E ≃L[Real] E) :
    ContDiffOn Real ∞ (map A) {x | 0 < denominator A x} := by
  apply ContDiffOn.smul
  · apply ContDiffOn.inv
    · exact (contDiff_denominator A).contDiffOn.sqrt (fun _ hx => ne_of_gt hx)
    · exact fun _ hx => ne_of_gt (Real.sqrt_pos.mpr hx)
  · exact A.contDiff.contDiffOn

private theorem norm_sq_scaled (d : Real) (hd : 0 < d) (v : E) :
    ‖(Real.sqrt d)⁻¹ • v‖ ^ 2 = ‖v‖ ^ 2 / d := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hd.le]
  ring

theorem norm_sq_map (A : E ≃L[Real] E) {x : E} (hx : 0 < denominator A x) :
    ‖map A x‖ ^ 2 = ‖A x‖ ^ 2 / denominator A x :=
  norm_sq_scaled _ hx _

theorem denominator_symm_map (A : E ≃L[Real] E) {x : E}
    (hx : 0 < denominator A x) : denominator A.symm (map A x) = (denominator A x)⁻¹ := by
  have he : A.symm (map A x) = (Real.sqrt (denominator A x))⁻¹ • x := by
    simp only [map, map_smul, A.symm_apply_apply]
  rw [denominator, he, norm_sq_scaled _ hx, norm_sq_map A hx]
  have hd : denominator A x ≠ 0 := ne_of_gt hx
  field_simp
  simp [denominator]

theorem map_mem_inverse_domain (A : E ≃L[Real] E) {x : E}
    (hx : 0 < denominator A x) : 0 < denominator A.symm (map A x) := by
  rw [denominator_symm_map A hx]
  exact inv_pos.mpr hx

theorem map_symm_map (A : E ≃L[Real] E) {x : E} (hx : 0 < denominator A x) :
    map A.symm (map A x) = x := by
  rw [map, denominator_symm_map A hx, Real.sqrt_inv, inv_inv]
  simp only [map, map_smul, A.symm_apply_apply, smul_smul]
  rw [mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hx)), one_smul]

theorem closedBall_subset_domain (A : E ≃L[Real] E) :
    closedBall (0 : E) 1 ⊆ {x | 0 < denominator A x} := by
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  change 0 < 1 + ‖A x‖ ^ 2 - ‖x‖ ^ 2
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hAx : A x ≠ 0 := fun h => hx0 (A.injective (by simpa using h))
    have hpos : 0 < ‖A x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hAx)
    nlinarith [norm_nonneg x]

theorem map_mem_closedBall_iff (A : E ≃L[Real] E) {x : E}
    (hx : 0 < denominator A x) :
    map A x ∈ closedBall (0 : E) 1 ↔ x ∈ closedBall (0 : E) 1 := by
  simp only [mem_closedBall, dist_zero_right]
  have hnorm := norm_sq_map A hx
  have hle : ‖map A x‖ ^ 2 ≤ 1 ↔ ‖x‖ ^ 2 ≤ 1 := by
    rw [hnorm, div_le_one hx]
    dsimp [denominator]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    have hs := hle.mp (by nlinarith [norm_nonneg (map A x)])
    nlinarith [norm_nonneg x]
  · intro h
    have hs := hle.mpr (by nlinarith [norm_nonneg x])
    nlinarith [norm_nonneg (map A x)]



def neighborhood (A : E ≃L[Real] E) : OpenPartialHomeomorph E E where
  toFun := map A
  invFun := map A.symm
  source := {x | 0 < denominator A x}
  target := {x | 0 < denominator A.symm x}
  map_source' _ hx := map_mem_inverse_domain A hx
  map_target' _ hx := map_mem_inverse_domain A.symm hx
  left_inv' _ hx := map_symm_map A hx
  right_inv' _ hx := map_symm_map A.symm hx
  open_source := isOpen_lt continuous_const (contDiff_denominator A).continuous
  open_target := isOpen_lt continuous_const (contDiff_denominator A.symm).continuous
  continuousOn_toFun := (contDiffOn_map A).continuousOn
  continuousOn_invFun := (contDiffOn_map A.symm).continuousOn

theorem closedBall_subset_source (A : E ≃L[Real] E) :
    closedBall (0 : E) 1 ⊆ (neighborhood A).source :=
  closedBall_subset_domain A

theorem closedBall_subset_target (A : E ≃L[Real] E) :
    closedBall (0 : E) 1 ⊆ (neighborhood A).target :=
  closedBall_subset_domain A.symm

theorem contMDiffOn_neighborhood (A : E ≃L[Real] E) :
    ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ (neighborhood A) (neighborhood A).source :=
  (contDiffOn_map A).contMDiffOn

theorem contMDiffOn_neighborhood_symm (A : E ≃L[Real] E) :
    ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ (neighborhood A).symm (neighborhood A).target :=
  (contDiffOn_map A.symm).contMDiffOn

theorem image_closedBall (A : E ≃L[Real] E) :
    neighborhood A '' closedBall (0 : E) 1 = closedBall 0 1 := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (map_mem_closedBall_iff A (closedBall_subset_domain A hx)).mpr hx
  · intro y hy
    refine ⟨map A.symm y, ?_, ?_⟩
    · exact (map_mem_closedBall_iff A.symm (closedBall_subset_domain A.symm hy)).mpr hy
    · exact map_symm_map A.symm (closedBall_subset_domain A.symm hy)

theorem apply_of_mem_sphere (A : E ≃L[Real] E) {x : E} (hx : x ∈ sphere (0 : E) 1) :
    neighborhood A x = ‖A x‖⁻¹ • A x := by
  have hnorm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  change (Real.sqrt (1 + ‖A x‖ ^ 2 - ‖x‖ ^ 2))⁻¹ • A x = _
  rw [hnorm]
  simp

end Poincare.Manifold.Schoenflies.LinearBall
