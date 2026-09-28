import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceAffineWeakTransport









noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Metric

namespace PoincareConjecture



theorem m64SourceAffine_mapsTo_closedBall (a : LoopPlane) (s : ℝ) (hs : s ≠ 0)
    {kappa : ℝ} (hk : 0 ≤ kappa)
    (hD : ‖(m64SourceScale s hs).toContinuousLinearMap‖ ≤ kappa)
    (b : LoopPlane) (r : ℝ) :
    MapsTo (m64SourceAffine a s hs) (closedBall b r)
      (closedBall (m64SourceAffine a s hs b) (kappa * r)) := by
  intro p hp
  apply mem_closedBall.mpr
  exact (m64SourceAffine_dist_le a s hs p b).trans
    ((mul_le_mul_of_nonneg_right hD (dist_nonneg)).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall.mp hp) hk))



theorem m64SourceAffine_mapsTo_ball (a : LoopPlane) (s : ℝ) (hs : s ≠ 0)
    {kappa R rho : ℝ} (hk : 0 ≤ kappa)
    (hD : ‖(m64SourceScale s hs).toContinuousLinearMap‖ ≤ kappa)
    (hsmall : kappa * R < rho) :
    MapsTo (m64SourceAffine a s hs) (closedBall 0 R) (ball a rho) := by
  have hzero : m64SourceAffine a s hs 0 = a := by
    change a + m64SourceScale s hs 0 = a
    rw [map_zero, add_zero]
  intro p hp
  have h := m64SourceAffine_mapsTo_closedBall a s hs hk hD 0 R hp
  rw [hzero] at h
  exact mem_ball.mpr ((mem_closedBall.mp h).trans_lt hsmall)




theorem m64SourceCoordinate_holder {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) {u : LoopPlane → E} {H : E → F}
    {kappa C beta R rho : ℝ} {L : NNReal}
    (hk : 0 ≤ kappa) (hC : 0 ≤ C) (hbeta : 0 ≤ beta)
    (hD : ‖(m64SourceScale s hs).toContinuousLinearMap‖ ≤ kappa)
    (hsmall : kappa * R ≤ rho) (hLip : LipschitzWith L H)
    (hholder : ∀ x ∈ closedBall a rho, ∀ y ∈ closedBall a rho,
      dist (u x) (u y) ≤ C * dist x y ^ beta) :
    ∀ x ∈ closedBall (0 : LoopPlane) R, ∀ y ∈ closedBall (0 : LoopPlane) R,
      dist (H (u (m64SourceAffine a s hs x))) (H (u (m64SourceAffine a s hs y))) ≤
        (L * C * kappa ^ beta) * dist x y ^ beta := by
  have hzero : m64SourceAffine a s hs 0 = a := by
    change a + m64SourceScale s hs 0 = a
    rw [map_zero, add_zero]
  have hmaps : MapsTo (m64SourceAffine a s hs) (closedBall 0 R) (closedBall a rho) := by
    intro z hz
    have h := m64SourceAffine_mapsTo_closedBall a s hs hk hD 0 R hz
    rw [hzero] at h
    exact closedBall_subset_closedBall hsmall h
  intro x hx y hy
  have hd : dist (m64SourceAffine a s hs x) (m64SourceAffine a s hs y) ≤
      kappa * dist x y := (m64SourceAffine_dist_le a s hs x y).trans
    (mul_le_mul_of_nonneg_right hD dist_nonneg)
  calc
    _ ≤ L * dist (u (m64SourceAffine a s hs x)) (u (m64SourceAffine a s hs y)) :=
      hLip.dist_le_mul _ _
    _ ≤ L * (C * dist (m64SourceAffine a s hs x) (m64SourceAffine a s hs y) ^ beta) :=
      mul_le_mul_of_nonneg_left (hholder _ (hmaps hx) _ (hmaps hy)) L.coe_nonneg
    _ ≤ L * (C * (kappa * dist x y) ^ beta) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd hbeta) hC) L.coe_nonneg
    _ = _ := by rw [Real.mul_rpow hk dist_nonneg]; ring

end PoincareConjecture
