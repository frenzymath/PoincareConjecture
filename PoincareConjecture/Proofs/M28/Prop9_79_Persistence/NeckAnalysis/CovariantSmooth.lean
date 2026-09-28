import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.ModelChristoffel

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

theorem contDiff_roundCylinderChristoffel {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (a b d : Fin 3) :
    ContDiff ℝ ∞ (fun p => roundCylinderChristoffel u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) := by
  simp_rw [roundCylinderChristoffel_chosen_chart hu]
  exact contDiff_cylinderModelChristoffel a b d

theorem contDiff_roundCylinderGram (u : ℝ) (q : UnitTwoSphere)
    (a b : Fin 3) :
    ContDiff ℝ ∞ (fun p => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) := by
  have hf : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
      2 * (1-u) * sphereChartConformalFactor p.1) :=
    by
      convert ((contDiff_const : ContDiff ℝ ∞
        (fun _ : RoundCylinderCoordinates => 2 * (1-u))).smul
          (contDiff_sphereChartConformalFactor.comp contDiff_fst)) using 1
      funext p
      simp [smul_eq_mul]
  simp_rw [roundCylinderGram_chosen_chart]
  fin_cases a <;> fin_cases b <;> dsimp [Matrix.diagonal] <;>
    first | exact hf | exact contDiff_const

theorem contDiffOn_roundCylinderTensorDerivative {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) {S : Set RoundCylinderCoordinates} (hS : IsOpen S)
    {r : ℕ} {T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ}
    (hT : ∀ a, ContDiffOn ℝ ∞ (fun p => T p a) S) :
    ∀ a, ContDiffOn ℝ ∞ (fun p => roundCylinderTensorDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) T p a) S := by
  intro a p hp
  have ht (b : Fin r → Fin 3) : ContDiffAt ℝ ∞ (fun y => T y b) p :=
    (hT b).contDiffAt (hS.mem_nhds hp)
  have hd := ((ht (fun i => a i.succ)).fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := roundCylinderCoordinateBasis (a 0)))
  have hc : ContDiffAt ℝ ∞ (fun y => ∑ i : Fin r, ∑ j : Fin 3,
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y
        j (a 0) (a i.succ) * T y (Function.update (fun k => a k.succ) i j)) p := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (contDiff_roundCylinderChristoffel hu q j (a 0) (a i.succ)).contDiffAt.mul
      (ht _)
  exact (hd.sub hc).contDiffWithinAt

theorem contDiffOn_roundCylinderIteratedDerivative {epsilon u : ℝ} (hu : u < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn epsilon B)
    (q : UnitTwoSphere) (k : ℕ) :
    ∀ a, ContDiffOn ℝ ∞ (fun p => roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k p a)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
  induction k with
  | zero =>
      intro a
      exact (hB q (a 0) (a 1)).sub
        (contDiff_roundCylinderGram u q (a 0) (a 1)).contDiffOn
  | succ k ih =>
      exact contDiffOn_roundCylinderTensorDerivative hu q
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).open_target.prod isOpen_Ioo) ih

end PoincareConjecture.Proofs.M28.NeckAnalysis
