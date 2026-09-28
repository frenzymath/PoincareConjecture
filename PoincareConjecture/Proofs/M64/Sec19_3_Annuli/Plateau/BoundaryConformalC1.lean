import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryDifferentialExtension
import PoincareConjecture.Proofs.M64.Mathlib.TransverseProjection

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped ContDiff Topology

namespace PoincareConjecture

private theorem m64ClosedHalfDisk_uniqueDiff {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) := by
  let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hK : Convex ℝ K := (convex_closedBall _ _).inter
    ((convex_Ici (0 : ℝ)).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  apply uniqueDiffOn_convex hK
  let z := (r / 2) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hz : z ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      change ‖(r / 2) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ < r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr), PiLp.norm_single,
        Real.norm_eq_abs, abs_one, mul_one]
      exact half_lt_self hr
    · change 0 < z 1
      simpa only [z, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul,
        mul_one] using half_pos hr
  exact ⟨z, mem_interior_iff_mem_nhds.mpr (mem_of_superset (hU.mem_nhds hz) hUK)⟩

theorem m64Conformal_contDiffOn_of_transverse {N : ℕ} {R : ℝ} (hR : 0 < R)
    (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hc : ContinuousOn u (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hsmooth : ContDiffOn ℝ 1 u (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (G : LoopPlane → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hG : ContinuousOn G (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hsymm : ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ∀ v : EuclideanSpace ℝ (Fin N), v ≠ 0 → 0 < G z v v)
    (hconformal : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      G z (fderiv ℝ u z (EuclideanSpace.single 0 1))
          (fderiv ℝ u z (EuclideanSpace.single 0 1)) =
        G z (fderiv ℝ u z (EuclideanSpace.single 1 1))
          (fderiv ℝ u z (EuclideanSpace.single 1 1)) ∧
      G z (fderiv ℝ u z (EuclideanSpace.single 0 1))
        (fderiv ℝ u z (EuclideanSpace.single 1 1)) = 0)
    (j : Fin N)
    (htransverse : ContDiffOn ℝ 1 (m64TransverseProjection j ∘ u)
      (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1})) :
    ContDiffOn ℝ 1 u (closedBall (0 : LoopPlane) (R / 4) ∩ {z | 0 ≤ z 1}) := by
  let Y := m64TransverseProjection j ∘ u
  let K := closedBall (0 : LoopPlane) R ∩ {z : LoopPlane | 0 ≤ z 1}
  let U := ball (0 : LoopPlane) R ∩ {z : LoopPlane | 0 < z 1}
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hDY : ContinuousOn (fderivWithin ℝ Y K) K :=
    htransverse.continuousOn_fderivWithin (m64ClosedHalfDisk_uniqueDiff hR) le_rfl
  let T := fun z a => (fderivWithin ℝ Y K z (EuclideanSpace.single 0 1) a : ℂ) -
    I * (fderivWithin ℝ Y K z (EuclideanSpace.single 1 1) a : ℂ)
  have hT : ContinuousOn T K := by
    apply continuousOn_pi.mpr
    intro a
    have h0 := (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_continuousOn
      (hDY.clm_apply (continuousOn_const (c := EuclideanSpace.single 0 1)))
    have h1 := (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_continuousOn
      (hDY.clm_apply (continuousOn_const (c := EuclideanSpace.single 1 1)))
    exact (continuous_ofReal.comp_continuousOn h0).sub
      (continuousOn_const.mul (continuous_ofReal.comp_continuousOn h1))
  have hTeq (z : LoopPlane) (hz : z ∈ U) (a : Fin N) (haj : a ≠ j) :
      T z a = (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ 0) a : ℂ) -
        I * (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ 1) a : ℂ) := by
    have hn : K ∈ 𝓝 z := mem_of_superset (hU.mem_nhds hz) hUK
    have hd := m64TransverseProjection_fderiv j
      ((hsmooth.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    simp only [T, Y, fderivWithin_of_mem_nhds hn, hd,
      ContinuousLinearMap.comp_apply, m64TransverseProjection_apply, if_neg haj,
      EuclideanSpace.basisFun_apply]
  obtain ⟨D, hD, hDeq⟩ := M64Boundary.exists_continuous_full_differential hR u hsmooth G
    hG hsymm hpos
    (by simpa only [EuclideanSpace.basisFun_apply] using fun z hz => (hconformal z hz).1)
    (by simpa only [EuclideanSpace.basisFun_apply] using fun z hz => (hconformal z hz).2)
    j T hT hTeq
  exact M64Boundary.contDiffOn_halfDisk_of_continuous_differential hR u hc hsmooth D hD hDeq

end PoincareConjecture
