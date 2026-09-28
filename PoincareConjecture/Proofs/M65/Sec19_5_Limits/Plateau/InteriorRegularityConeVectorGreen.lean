import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeGreenDisk











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior




theorem coneCartesianField_clm {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) {g : EuclideanSpace ℝ (Fin 3) → E}
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3))
    (v d : ℝ → EuclideanSpace ℝ (Fin 3)) (s θ : ℝ) (i : Fin 2)
    (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ)) :
    coneCartesianField (L ∘ g) r v0 v d s θ i =
      L (coneCartesianField g r v0 v d s θ i) := by
  have h := L.hasFDerivAt.comp (coneCoordinates r v0 v s θ) hg.hasFDerivAt
  simp only [coneCartesianField, h.fderiv, ContinuousLinearMap.comp_apply, map_smul, map_add]




theorem coneDisk_green_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {g : EuclideanSpace ℝ (Fin 3) → E}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi)
    (hper : v (-Real.pi) = v Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hinc : ∀ t ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    (∫ z in closedBall x r, L (coneDiskField g r v0 v d x i z) * test z +
      L (coneDiskMap g r v0 v x z) *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * ∫ θ in (-Real.pi)..Real.pi,
        L (g (v θ)) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i := by
  have hgL : ContDiffOn ℝ 1 (L ∘ g) (ball 0 (2 * ρ)) :=
    L.contDiff.comp_contDiffOn hg
  have hDL : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
      ‖fderiv ℝ (L ∘ g) y‖ ≤ ‖L‖ * K := by
    intro y hy
    have hym : y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * ρ) :=
      (closedBall_subset_ball (by linarith)) hy
    have hgd := (hg.contDiffAt (isOpen_ball.mem_nhds hym)).differentiableAt one_ne_zero
    rw [(L.hasFDerivAt.comp y hgd.hasFDerivAt).fderiv]
    exact (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hD y hy) (norm_nonneg L))
  have h := (coneDisk_green hr hρ (mul_nonneg (norm_nonneg L) hK)
    hv hper hgL h0 hvb hd hinc hDL x test ht i).2
  calc
    _ = ∫ z in closedBall x r, coneDiskField (L ∘ g) r v0 v d x i z * test z +
        coneDiskMap (L ∘ g) r v0 v x z *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      apply setIntegral_congr_fun isClosed_closedBall.measurableSet
      intro z hz
      have hm : coneCoordinates r v0 v (polarCoordinates x z).1 (polarCoordinates x z).2 ∈
          ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * ρ) :=
        (closedBall_subset_ball (by linarith)) (coneDisk_coordinates_mem hr h0 hvb x hz)
      have hgd := (hg.contDiffAt (isOpen_ball.mem_nhds hm)).differentiableAt one_ne_zero
      simp only [coneDiskField, coneCartesianField_clm L r v0 v d _ _ i hgd,
        coneDiskMap, Function.comp_apply]
    _ = _ := h

end PoincareConjecture.M65Interior
