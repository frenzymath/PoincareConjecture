import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeMidpoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture.M64BoundaryCone

open M65Interior M65Boundary

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem coneCartesianField_clm {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) {g : C → E}
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (s θ : ℝ) (i : Fin 2)
    (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ)) :
    coneCartesianField (L ∘ g) r v0 v d s θ i =
      L (coneCartesianField g r v0 v d s θ i) := by
  have h := L.hasFDerivAt.comp (coneCoordinates r v0 v s θ) hg.hasFDerivAt
  simp only [coneCartesianField, h.fderiv, ContinuousLinearMap.comp_apply, map_smul, map_add]

theorem midpoint_halfCone_green_clm [CompleteSpace C] [ProperSpace C] {N : ℕ}
    {g : C → EuclideanSpace ℝ (Fin N)}
    {v d : ℝ → C} {r ρ K : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hC : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ θ in s..t, d θ)
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) (j : Fin N) :
    let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      coneDiskField g r m v d 0 i z j * test z + coneDiskMap g r m v 0 z j *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        g (v θ) j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
        ∫ s in (-r)..r, g (halfConeDiameter r (v 0) (v Real.pi) s) j *
          test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := EuclideanSpace.proj j
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  have h0 : m ∈ closedBall 0 ρ := midpoint_mem_closedBall
    (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
  have hDL (y : C) (hy : y ∈ closedBall 0 ρ) :
      ‖fderiv ℝ (L ∘ g) y‖ ≤ ‖L‖ * K := by
    have hym : y ∈ ball (0 : C) (2 * ρ) :=
      (closedBall_subset_ball (by linarith)) hy
    have hgd := (hg.contDiffAt (isOpen_ball.mem_nhds hym)).differentiableAt one_ne_zero
    rw [(L.hasFDerivAt.comp y hgd.hasFDerivAt).fderiv]
    exact (L.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hD y hy) (norm_nonneg L))
  have h := (midpoint_halfCone_green hr hρ (mul_nonneg (norm_nonneg L) hC) hv
    (L.contDiff.comp_contDiffOn hg) hvb hd hinc hDL test ht i).2
  calc
    _ = ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        coneDiskField (L ∘ g) r m v d 0 i z * test z +
          coneDiskMap (L ∘ g) r m v 0 z *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      apply setIntegral_congr_fun (measurableSet_closedBall.inter
        (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet)
      intro z hz
      have hz' : z ∈ closedBall (0 : LoopPlane) r ∩ {z | (0 : LoopPlane) 1 ≤ z 1} := hz
      rw [← polarCoordinates_preimage_halfRectangle] at hz'
      have hm := coneCoordinates_mem_closedBall hr h0 (hvb hz'.2) hz'.1
      have hgd := (hg.contDiffAt (isOpen_ball.mem_nhds
        ((closedBall_subset_ball (by linarith : ρ < 2 * ρ)) hm))).differentiableAt one_ne_zero
      simp only [coneDiskField, coneCartesianField_clm L r m v d _ _ i hgd,
        coneDiskMap, Function.comp_apply]
      rfl
    _ = _ := h

end PoincareConjecture.M64BoundaryCone
