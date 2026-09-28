import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamRadialPullbackTest












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture



theorem m64MatchingGreen_seam_pullback
    {m : ℕ} {K : Set LoopPlane} (hK : IsCompact K) (hKO : K ⊆ m64AnnulusSeamDomain)
    (u0 u1 W0 W1 : LoopPlane → EuclideanSpace ℝ (Fin m)) {i : Fin 2}
    (hu0 : MemLp u0 2 (volume.restrict K)) (hu1 : MemLp u1 2 (volume.restrict K))
    (hW0 : MemLp W0 2 (volume.restrict K)) (hW1 : MemLp W1 2 (volume.restrict K))
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in K, phi p • W1 p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u1 p) =
      (∫ p in K, phi p • W0 p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u0 p))
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (htest : i = 1 ∨ ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    (∫ p in K, m64AnnulusSeamExtend phi p • W1 p) +
      (∫ p in K,
        m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p • u1 p) =
    (∫ p in K, m64AnnulusSeamExtend phi p • W0 p) +
      (∫ p in K,
        m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p • u0 p) := by
  let E := EuclideanSpace ℝ (Fin m)
  have hflux (psi : LoopPlane → ℝ) (L : ℝ≥0) (hL : LipschitzWith L psi)
      (hc : HasCompactSupport psi) :
      (∫ p in K, psi p • W1 p) +
        (∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u1 p) =
      (∫ p in K, psi p • W0 p) +
        (∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u0 p) :=
    m64MatchingGreen_compact_lipschitz hK u0 u1 W0 W1 hu0 hu1 hW0 hW1 hgreen hL hc
  rcases htest with rfl | hseam
  · obtain ⟨psi, Z, hpM, hZM, hc, hwpsi, heq⟩ :=
      m64_exists_compact_radial_seam_test hK hKO hp
    have h := m64MatchingGreen_compact_directional hK.measurableSet u0 u1 W0 W1
      hu0 hu1 hW0 hW1 hflux hpM hZM hwpsi hc
    have hval (w : LoopPlane → E) : (∫ p in K, psi p • w p) =
        ∫ p in K, m64AnnulusSeamExtend phi p • w p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hpK
      rw [(heq p hpK).1]
    have hder (w : LoopPlane → E) : (∫ p in K, Z p • w p) =
        ∫ p in K,
          m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single (1 : Fin 2) 1)) p •
            w p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hpK
      rw [(heq p hpK).2]
    rw [hval, hder, hval, hder] at h
    exact h
  · obtain ⟨psi, L, hL, hc, heq⟩ := m64_exists_compact_lipschitz_seam_test hK hKO hp hseam
    have h := hflux psi L hL hc
    have hn : ∀ᵐ p ∂volume.restrict K, p 0 ≠ 0 := by
      apply ae_restrict_of_ae
      apply ae_iff.mpr
      simpa only [not_not] using m64_cut_line_null 0
    have hval (w : LoopPlane → E) : (∫ p in K, psi p • w p) =
        ∫ p in K, m64AnnulusSeamExtend phi p • w p := by
      apply integral_congr_ae
      filter_upwards [hn, ae_restrict_mem hK.measurableSet] with p hp0 hpK
      rw [(heq p hpK hp0).1]
      rfl
    have hder (w : LoopPlane → E) :
        (∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • w p) =
        ∫ p in K,
          m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p • w p := by
      apply integral_congr_ae
      filter_upwards [hn, ae_restrict_mem hK.measurableSet] with p hp0 hpK
      rw [(heq p hpK hp0).2 i]
      rfl
    rw [hval, hder, hval, hder] at h
    exact h

end PoincareConjecture
