import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.FilledModel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

def horizontal (p : E3) : E2 := WithLp.toLp 2 ![p 0, p 1]

theorem horizontal_contDiff : ContDiff Real ∞ horizontal := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff Real ∞ (fun p : E3 => p 0)
    fun_prop
  · change ContDiff Real ∞ (fun p : E3 => p 1)
    fun_prop

@[simp] theorem horizontal_vector (x y z : Real) :
    horizontal (vector x y z) = WithLp.toLp 2 ![x, y] := rfl

def graphCoordinates (b : E2 → Real) (hb : ContDiff Real ∞ b) :
    Diffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞ where
  toFun p := vector (p.1 0) (p.1 1) (p.2 + b p.1)
  invFun p := (horizontal p, p 2 - b (horizontal p))
  left_inv p := by
    have hq : horizontal (vector (p.1 0) (p.1 1) (p.2 + b p.1)) = p.1 := by
      ext i
      fin_cases i <;> rfl
    apply Prod.ext
    · exact hq
    · simp only [vector_two, hq, add_sub_cancel_right]
  right_inv p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change p 2 - b (horizontal p) + b (horizontal p) = p 2
      ring
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff Real ∞ (fun p : E2 × Real => p.1 0)
      fun_prop
    · change ContDiff Real ∞ (fun p : E2 × Real => p.1 1)
      fun_prop
    · change ContDiff Real ∞ (fun p : E2 × Real => p.2 + b p.1)
      exact contDiff_snd.add (hb.comp contDiff_fst)
  contMDiff_invFun := (horizontal_contDiff.prodMk
    ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.sub
      (hb.comp horizontal_contDiff))).contMDiff

theorem graphCoordinates_apply (b : E2 → Real) (hb : ContDiff Real ∞ b) (p : E2 × Real) :
    graphCoordinates b hb p = vector (p.1 0) (p.1 1) (p.2 + b p.1) := rfl

theorem horizontal_graphCoordinates (b : E2 → Real) (hb : ContDiff Real ∞ b) (p : E2 × Real) :
    horizontal (graphCoordinates b hb p) = p.1 := by
  ext i
  fin_cases i <;> rfl

def lowerGraph (q : E2) : Real := -Real.sqrt (1 - ‖q‖^2) - (q 0)^2

theorem lowerGraph_contDiffOn : ContDiffOn Real ∞ lowerGraph (ball (0 : E2) 1) := by
  exact (((contDiff_const.sub (contDiff_id.norm_sq Real)).contDiffOn.sqrt
    (fun q hq => ne_of_gt (by
      change 0 < 1 - ‖q‖^2
      have hn := mem_ball_zero_iff.mp hq
      nlinarith [norm_nonneg q]))).neg).sub
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.pow 2).contDiffOn

theorem lowerGraph_small {q : E2} (hq : ‖q‖ ≤ 1/8) : |lowerGraph q + 1| ≤ 1/64 := by
  have hn : ‖q‖^2 ≤ 1/64 := by nlinarith [norm_nonneg q]
  have hpos : 0 ≤ 1-‖q‖^2 := by linarith
  have hs := Real.sq_sqrt hpos
  have hroot := Real.sqrt_nonneg (1-‖q‖^2)
  have hle : Real.sqrt (1-‖q‖^2) ≤ 1 := by nlinarith [sq_nonneg ‖q‖]
  have hge : 1-‖q‖^2 ≤ Real.sqrt (1-‖q‖^2) := by
    nlinarith [sq_nonneg (1-‖q‖^2-Real.sqrt (1-‖q‖^2))]
  have hnorm := norm_sq_two q
  rw [abs_le]
  unfold lowerGraph
  constructor <;> nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]

theorem lowerGraph_mem_surface {q : E2} (hq : ‖q‖ < 1) :
    polynomial (vector (q 0) (q 1) (lowerGraph q)) = 1 := by
  have hp : 0 ≤ 1-‖q‖^2 := by nlinarith [norm_nonneg q]
  unfold polynomial lowerGraph
  simp only [vector_zero, vector_one, vector_two, sub_add_cancel,
    neg_sq, Real.sq_sqrt hp]
  rw [norm_sq_two]
  ring

end Poincare.Manifold.Schoenflies.Saddle
