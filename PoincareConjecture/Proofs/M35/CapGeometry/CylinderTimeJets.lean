import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35

private theorem weighted_sum_linear {r : ℕ}
    (G T S : Fin r → Fin 3 → ℝ) (A B : ℝ) :
    (∑ i, ∑ j, G i j * (A * T i j - B * S i j)) =
      A * (∑ i, ∑ j, G i j * T i j) - B * (∑ i, ∑ j, G i j * S i j) := by
  calc
    _ = ∑ i, ∑ j, (A * (G i j * T i j) - B * (G i j * S i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.mul_sum]

theorem roundCylinderIteratedDerivative_time_affine
    (B : ℝ → RoundCylinderTwoTensor)
    (haffine : ∀ u ≤ 0, ∀ z v w,
      B u z v w = (1 + 2 * u) * B 0 z v w - 2 * u * B (-1 / 2) z v w)
    (epsilon : ℝ) (hs0 : RoundCylinderTensorSmoothOn epsilon (B 0))
    (hshalf : RoundCylinderTensorSmoothOn epsilon (B (-1 / 2)))
    (u : ℝ) (hu : u ≤ 0) (q : UnitTwoSphere) (k : ℕ)
    (p : RoundCylinderCoordinates)
    (hp : p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
      Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) (B u) k p a =
      (1 + 2 * u) * roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (B 0) k p a -
      2 * u * roundCylinderIteratedDerivative (-1 / 2)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (B (-1 / 2)) k p a := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let U := c.target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  have hU : IsOpen U := c.open_target.prod isOpen_Ioo
  have hGamma (s : ℝ) (hs : s < 1) (y : RoundCylinderCoordinates) (i j l : Fin 3) :
      roundCylinderChristoffel s c y i j l = roundCylinderChristoffel 0 c y i j l := by
    rw [roundCylinderChristoffel_eq hs, roundCylinderChristoffel_eq zero_lt_one]
  have hcoeff (y : RoundCylinderCoordinates) (i j : Fin 3) :
      roundCylinderTensorCoefficient (B u) c y i j =
        (1 + 2 * u) * roundCylinderTensorCoefficient (B 0) c y i j -
          2 * u * roundCylinderTensorCoefficient (B (-1 / 2)) c y i j :=
    haffine u hu _ _ _
  have hmodel (y : RoundCylinderCoordinates) (i j : Fin 3) :
      roundCylinderGram u c y i j = (1 + 2 * u) * roundCylinderGram 0 c y i j -
        2 * u * roundCylinderGram (-1 / 2) c y i j := by
    unfold roundCylinderGram roundCylinderTensorCoefficient EvolvingRoundCylinderMetric
    ring
  change roundCylinderIteratedDerivative u c (B u) k p a =
    (1 + 2 * u) * roundCylinderIteratedDerivative 0 c (B 0) k p a -
      2 * u * roundCylinderIteratedDerivative (-1 / 2) c (B (-1 / 2)) k p a
  induction k generalizing p with
  | zero =>
    change roundCylinderTensorCoefficient (B u) c p (a 0) (a 1) -
      roundCylinderGram u c p (a 0) (a 1) = _
    rw [hcoeff, hmodel]
    change _ = (1 + 2 * u) *
      (roundCylinderTensorCoefficient (B 0) c p (a 0) (a 1) -
        roundCylinderGram 0 c p (a 0) (a 1)) -
      2 * u * (roundCylinderTensorCoefficient (B (-1 / 2)) c p (a 0) (a 1) -
        roundCylinderGram (-1 / 2) c p (a 0) (a 1))
    ring
  | succ k ih =>
    have hs0p (i j : Fin 3) : ContDiffAt ℝ ∞
        (fun y => roundCylinderTensorCoefficient (B 0) c y i j) p :=
      (hs0 q i j p hp).contDiffAt (hU.mem_nhds hp)
    have hshp (i j : Fin 3) : ContDiffAt ℝ ∞
        (fun y => roundCylinderTensorCoefficient (B (-1 / 2)) c y i j) p :=
      (hshalf q i j p hp).contDiffAt (hU.mem_nhds hp)
    have he : (fun y => roundCylinderIteratedDerivative u c (B u) k y (fun i => a i.succ))
        =ᶠ[𝓝 p] (fun y => (1 + 2 * u) *
          roundCylinderIteratedDerivative 0 c (B 0) k y (fun i => a i.succ) -
          2 * u * roundCylinderIteratedDerivative (-1 / 2) c (B (-1 / 2)) k y
            (fun i => a i.succ)) :=
      Filter.mem_of_superset (hU.mem_nhds hp) (fun y hy => ih y hy _)
    have hd0 := (contDiffAt_roundCylinderIteratedDerivative zero_lt_one q (B 0)
      p hs0p k (fun i => a i.succ)).differentiableAt (by simp)
    have hdh := (contDiffAt_roundCylinderIteratedDerivative
      (by norm_num : (-1 / 2 : ℝ) < 1) q (B (-1 / 2)) p hshp k
        (fun i => a i.succ)).differentiableAt (by simp)
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    erw [he.fderiv_eq (𝕜 := ℝ)]
    rw [fderiv_fun_sub (hd0.const_mul (1 + 2 * u))
      (hdh.const_mul (2 * u)), fderiv_const_mul hd0, fderiv_const_mul hdh]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    simp_rw [hGamma u (hu.trans_lt zero_lt_one),
      hGamma (-1 / 2) (by norm_num : (-1 / 2 : ℝ) < 1), ih p hp]
    rw [weighted_sum_linear]
    dsimp only [c]
    ring!

end PoincareConjecture.M35
