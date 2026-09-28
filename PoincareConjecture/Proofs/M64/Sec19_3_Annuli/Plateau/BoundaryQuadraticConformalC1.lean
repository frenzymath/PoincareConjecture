import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTransverseC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConformalC1














set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture






theorem m64Conformal_quadratic_boundary_contDiffOn
    {N : ℕ} {R C H beta Lambda lower upper : ℝ} (hR : 0 < R)
    (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (hu : MemLp u 2 (volume.restrict (ball (0 : LoopPlane) R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball (0 : LoopPlane) R)))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun z => V i z j) (fun z => u z j)
      (ball (0 : LoopPlane) R))
    (hsmooth : ContDiffOn ℝ 2 u (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hc : ContinuousOn u (closedBall (0 : LoopPlane) (R / 2)))
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hbeta : 0 < beta) (hLambda : 0 ≤ Lambda)
    (hholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), ‖u z - u x‖ ≤ H * dist z x ^ beta)
    (j : Fin N)
    (hzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 →
      ∀ a : Fin N, a ≠ j → u z a = 0)
    (G : LoopPlane → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hG : ContinuousOn G (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hmetric : ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      (∀ v w, G z v w = G z w v) ∧
      (∀ v, lower * ‖v‖ ^ 2 ≤ G z v v) ∧ (∀ v, G z v v ≤ upper * ‖v‖ ^ 2))
    (hconformal : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      G z (fderiv ℝ u z (EuclideanSpace.single 0 1))
          (fderiv ℝ u z (EuclideanSpace.single 0 1)) =
        G z (fderiv ℝ u z (EuclideanSpace.single 1 1))
          (fderiv ℝ u z (EuclideanSpace.single 1 1)) ∧
      G z (fderiv ℝ u z (EuclideanSpace.single 0 1))
        (fderiv ℝ u z (EuclideanSpace.single 1 1)) = 0)
    (hgrowth : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ u z (EuclideanSpace.single i 1)‖ ^ 2)
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4),
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤ Lambda * r ^ (2 * beta)) :
    ContDiffOn ℝ 1 u (closedBall (0 : LoopPlane) (R / 256) ∩ {z | 0 ≤ z 1}) := by
  have hUK : (ball (0 : LoopPlane) R ∩ {z : LoopPlane | 0 < z 1}) ⊆
      (closedBall (0 : LoopPlane) R ∩ {z : LoopPlane | 0 ≤ z 1}) :=
    fun z hz => ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have htransverse := m64Conformal_transverse_contDiffOn hR u V hu hV hweak hsmooth hc
    hC hH hbeta hLambda hholder j hzero G hlower hupper
    (fun z hz => hmetric z (hUK hz)) hconformal hgrowth hdecay
  let r := R / 64
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrhalf : r ≤ R / 2 := by dsimp only [r]; linarith
  have hrR : r ≤ R := by dsimp only [r]; linarith
  have hK : (closedBall (0 : LoopPlane) r ∩ {z : LoopPlane | 0 ≤ z 1}) ⊆
      (closedBall (0 : LoopPlane) R ∩ {z : LoopPlane | 0 ≤ z 1}) :=
    fun z hz => ⟨closedBall_subset_closedBall hrR hz.1, hz.2⟩
  have hU : (ball (0 : LoopPlane) r ∩ {z : LoopPlane | 0 < z 1}) ⊆
      (ball (0 : LoopPlane) R ∩ {z : LoopPlane | 0 < z 1}) :=
    fun z hz => ⟨ball_subset_ball hrR hz.1, hz.2⟩
  have hpos : ∀ z ∈ closedBall (0 : LoopPlane) r ∩ {z : LoopPlane | 0 ≤ z 1},
      ∀ v : EuclideanSpace ℝ (Fin N), v ≠ 0 → 0 < G z v v := by
    intro z hz v hv
    exact (mul_pos hlower (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le
      ((hmetric z (hK hz)).2.1 v)
  have hfinish := m64Conformal_contDiffOn_of_transverse hr u
    (hc.mono (fun z hz => closedBall_subset_closedBall hrhalf hz.1))
    ((hsmooth.mono hU).of_le (by simp)) G (hG.mono hK)
    (fun z hz => (hmetric z (hK hz)).1) hpos
    (fun z hz => hconformal z (hU hz)) j htransverse
  have hquarter : r / 4 = R / 256 := by dsimp only [r]; ring
  simpa only [hquarter] using hfinish

end PoincareConjecture
