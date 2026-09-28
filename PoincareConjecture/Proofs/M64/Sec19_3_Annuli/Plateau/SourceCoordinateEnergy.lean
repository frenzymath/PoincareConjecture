import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceCoordinateWeakData
import PoincareConjecture.Proofs.M64.Mathlib.MeasurePreservingColumnEnergy










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace PoincareConjecture




theorem m64SourceCoordinate_energy_growth {m n : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) {rho R kappa K C beta : ℝ} {O : Set LoopPlane}
    (hR : 0 < R) (hk : 0 < kappa) (hK : 0 ≤ K)
    (hD : ‖(m64SourceScale s hs).toContinuousLinearMap‖ ≤ kappa)
    (hsmall : kappa * R ≤ rho) (hO : closedBall a (2 * rho) ⊆ O)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hDH : ∀ y, ‖fderiv ℝ H y‖ ≤ K)
    (henergy : ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r, ∑ i : Fin 2, ‖V i p‖ ^ 2) ≤ C * r ^ beta)
    (hW : ∀ i, MemLp
      (fun p => fderiv ℝ H (u (m64SourceAffine a s hs p))
        (m64SourceScaleFactor s i • V i (m64SourceAffine a s hs p)))
      2 (volume.restrict (ball (0 : LoopPlane) R))) :
    let Phi := m64SourceAffine a s hs
    let W := fun i p => fderiv ℝ H (u (Phi p)) (m64SourceScaleFactor s i • V i (Phi p))
    ∀ b ∈ closedBall (0 : LoopPlane) (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ p in closedBall b r, ∑ i : Fin 2, ‖W i p‖ ^ 2) ≤
        ((K * kappa) ^ 2 * C * kappa ^ beta) * r ^ beta := by
  let Phi := m64SourceAffine a s hs
  let W := fun i p => fderiv ℝ H (u (Phi p)) (m64SourceScaleFactor s i • V i (Phi p))
  have hzero : Phi 0 = a := by
    change a + m64SourceScale s hs 0 = a
    rw [map_zero, add_zero]
  change ∀ b ∈ closedBall (0 : LoopPlane) (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
    (∫ p in closedBall b r, ∑ i : Fin 2, ‖W i p‖ ^ 2) ≤
      ((K * kappa) ^ 2 * C * kappa ^ beta) * r ^ beta
  intro b hb r hr hrR
  have hb' : Phi b ∈ closedBall a rho := by
    have h := m64SourceAffine_mapsTo_closedBall a s hs hk.le hD 0 (R / 4) hb
    change Phi b ∈ closedBall (Phi 0) (kappa * (R / 4)) at h
    rw [hzero] at h
    exact closedBall_subset_closedBall
      ((mul_le_mul_of_nonneg_left (by linarith only [hR] : R / 4 ≤ R) hk.le).trans hsmall) h
  have hr' : kappa * r ∈ Ioc (0 : ℝ) rho :=
    ⟨mul_pos hk hr, (mul_le_mul_of_nonneg_left (hrR.trans (by linarith : R / 4 ≤ R))
      hk.le).trans hsmall⟩
  have hball : closedBall (Phi b) (kappa * r) ⊆ O :=
    (closedBall_subset_closedBall'
      (show kappa * r + dist (Phi b) a ≤ 2 * rho from by
        linarith [hr'.2, mem_closedBall.mp hb'])).trans hO
  have hlocal : closedBall b r ⊆ ball (0 : LoopPlane) R := by
    intro p hp
    apply mem_ball.mpr
    have hpb := mem_closedBall.mp hp
    have hb0 := mem_closedBall.mp hb
    linarith [dist_triangle p b (0 : LoopPlane)]
  have hnorm (i : Fin 2) (p : LoopPlane) : ‖W i p‖ ≤ (K * kappa) * ‖V i (Phi p)‖ := by
    calc
      _ ≤ K * ‖m64SourceScaleFactor s i • V i (Phi p)‖ :=
        ((fderiv ℝ H (u (Phi p))).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hDH _) (norm_nonneg _))
      _ = K * (‖m64SourceScaleFactor s i‖ * ‖V i (Phi p)‖) := by rw [norm_smul]
      _ ≤ K * (kappa * ‖V i (Phi p)‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ((m64SourceScale_factor_le_norm s hs i).trans hD)
          (norm_nonneg _)) hK
      _ = _ := by ring
  have hbound := m64MeasurePreserving_column_energy_le
    (m64SourceAffine_measurePreserving a s hs) Phi.measurableEmbedding
    isClosed_closedBall.measurableSet
    (m64SourceAffine_mapsTo_closedBall a s hs hk.le hD b r) V W
    (fun i => (hV i).mono_measure (Measure.restrict_mono_set volume hball))
    (fun i => (hW i).mono_measure (Measure.restrict_mono_set volume hlocal))
    (fun i p _ => hnorm i p)
  calc
    _ ≤ (K * kappa) ^ 2 * ∫ p in closedBall (Phi b) (kappa * r),
        ∑ i : Fin 2, ‖V i p‖ ^ 2 := hbound
    _ ≤ (K * kappa) ^ 2 * (C * (kappa * r) ^ beta) :=
      mul_le_mul_of_nonneg_left (henergy _ hb' _ hr') (sq_nonneg _)
    _ = _ := by rw [Real.mul_rpow hk.le hr.le]; ring

end PoincareConjecture
