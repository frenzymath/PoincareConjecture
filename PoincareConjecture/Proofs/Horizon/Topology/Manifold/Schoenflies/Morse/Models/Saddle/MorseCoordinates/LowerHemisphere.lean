import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.CriticalPoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.QuadraticPatch.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩

def lowerSphereGraph (q : E2) : E3 :=
  vector (q 0) (q 1) (-Real.sqrt (1 - ‖q‖^2))

theorem lowerSphereGraph_mem {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    lowerSphereGraph q ∈ sphere (0 : E3) 1 := by
  have hn := mem_ball_zero_iff.mp hq
  have hp : 0 ≤ 1 - ‖q‖^2 := by nlinarith [norm_nonneg q]
  have he : ‖lowerSphereGraph q‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, lowerSphereGraph,
      vector_zero, vector_one, vector_two, neg_sq, Real.sq_sqrt hp]
    rw [norm_sq_two]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (lowerSphereGraph q)]

theorem lowerSphereGraph_contDiffOn :
    ContDiffOn Real ∞ lowerSphereGraph (ball (0 : E2) 1) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffOn Real ∞ (fun q : E2 => q 0) _
    fun_prop
  · change ContDiffOn Real ∞ (fun q : E2 => q 1) _
    fun_prop
  · change ContDiffOn Real ∞ (fun q : E2 => -Real.sqrt (1-‖q‖^2)) _
    exact (((contDiff_const.sub (contDiff_id.norm_sq Real)).contDiffOn.sqrt
      (fun q hq => ne_of_gt (by
        change 0 < 1-‖q‖^2
        have hn := mem_ball_zero_iff.mp hq
        nlinarith [norm_nonneg q]))).neg)

private def lowerSphereMap (q : E2) : S2 :=
  Plane.unitRadialProjection saddlePoint (lowerSphereGraph q)

private theorem lowerSphereMap_coe {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    (lowerSphereMap q : E3) = lowerSphereGraph q := by
  exact congrArg Subtype.val (Plane.unitRadialProjection_apply_coe saddlePoint
    ⟨lowerSphereGraph q, lowerSphereGraph_mem hq⟩)

private theorem lowerSphereMap_smooth :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ lowerSphereMap (ball (0 : E2) 1) := by
  apply (Plane.contMDiffOn_unitRadialProjection (n := 2) (m := ∞) saddlePoint).comp
    lowerSphereGraph_contDiffOn.contMDiffOn
  intro q hq
  exact ne_zero_of_mem_unit_sphere ⟨lowerSphereGraph q, lowerSphereGraph_mem hq⟩

private theorem horizontal_mem_ball {p : S2} (hp : (p : E3) 2 < 0) :
    horizontal p ∈ ball (0 : E2) 1 := by
  have hn := EuclideanSpace.norm_sq_eq (p : E3)
  simp only [norm_eq_of_mem_sphere, one_pow, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs] at hn
  have hh : ‖horizontal p‖^2 = ((p : E3) 0)^2 + ((p : E3) 1)^2 := norm_sq_two _
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg (horizontal p), sq_pos_of_neg hp]

private theorem lowerSphereGraph_horizontal {p : S2} (hp : (p : E3) 2 < 0) :
    lowerSphereGraph (horizontal p) = (p : E3) := by
  have hn := EuclideanSpace.norm_sq_eq (p : E3)
  simp only [norm_eq_of_mem_sphere, one_pow, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs] at hn
  have hh : ‖horizontal p‖^2 = ((p : E3) 0)^2 + ((p : E3) 1)^2 := norm_sq_two _
  have hs : 1 - ‖horizontal p‖^2 = ((p : E3) 2)^2 := by linarith
  ext i
  fin_cases i
  · rfl
  · rfl
  · simp [lowerSphereGraph, hs, Real.sqrt_sq_eq_abs, abs_of_neg hp]

def lowerSphereChart : OpenPartialHomeomorph E2 S2 where
  toFun := lowerSphereMap
  invFun p := horizontal p
  source := ball 0 1
  target := {p | (p : E3) 2 < 0}
  map_source' q hq := by
    change (lowerSphereMap q : E3) 2 < 0
    rw [lowerSphereMap_coe hq]
    change -Real.sqrt (1-‖q‖^2) < 0
    have hn := mem_ball_zero_iff.mp hq
    exact neg_neg_of_pos (Real.sqrt_pos.mpr (by nlinarith [norm_nonneg q]))
  map_target' _ hp := horizontal_mem_ball hp
  left_inv' q hq := by
    rw [lowerSphereMap_coe hq]
    ext i
    fin_cases i <;> rfl
  right_inv' p hp := by
    apply Subtype.ext
    rw [lowerSphereMap_coe (horizontal_mem_ball hp)]
    exact lowerSphereGraph_horizontal hp
  open_source := isOpen_ball
  open_target := isOpen_lt
    ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).continuous.comp continuous_subtype_val)
    continuous_const
  continuousOn_toFun := lowerSphereMap_smooth.continuousOn
  continuousOn_invFun := (horizontal_contDiff.continuous.comp continuous_subtype_val).continuousOn

theorem lowerSphereChart_source : lowerSphereChart.source = ball (0 : E2) 1 := rfl

theorem lowerSphereChart_coe {q : E2} (hq : q ∈ lowerSphereChart.source) :
    (lowerSphereChart q : E3) = lowerSphereGraph q := lowerSphereMap_coe hq

theorem lowerSphereChart_smooth :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ lowerSphereChart lowerSphereChart.source :=
  lowerSphereMap_smooth

theorem lowerSphereChart_symm_smooth :
    ContMDiff (𝓡 2) (𝓡 2) ∞ lowerSphereChart.symm :=
  horizontal_contDiff.contMDiff.comp (contMDiff_coe_sphere (n := 2))

theorem lowerSphereChart_zero : lowerSphereChart 0 = saddlePoint := by
  apply Subtype.ext
  rw [lowerSphereChart_coe (mem_ball_self (by norm_num))]
  ext i
  fin_cases i <;> simp [lowerSphereGraph, saddlePoint]

theorem height_lowerSphereChart {q : E2} (hq : q ∈ lowerSphereChart.source) :
    height (lowerSphereChart q) = lowerGraph q := by
  rw [height_apply, lowerSphereChart_coe hq]
  rfl

end Poincare.Manifold.Schoenflies.Saddle
