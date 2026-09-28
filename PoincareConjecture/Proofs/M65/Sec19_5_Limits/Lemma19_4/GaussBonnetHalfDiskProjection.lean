import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetResidualPlane
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetHalfDiskResidual










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

open M65StrictTrace M65Gauss






theorem halfDisk_residual_projection {n : ℕ} [Nonempty (Fin n)]
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) (m : ℕ)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ : ContinuousOn Q (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ1 : ContDiffOn ℝ 1 Q (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hQne : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, Q z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      halfDiskGradient H r z = z ^ m • Q z)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    (hDQ1 : MemLp (fun z => fderiv ℝ Q z 1)
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im})))
    (hDQI : MemLp (fun z => fderiv ℝ Q z I)
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im}))) :
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
    let P := fun z => twoPlaneProjection (g.euclideanCoefficients (H z))
      (residualRealColumn (Q z)) (residualImagColumn (Q z))
    ContinuousOn P K ∧
      (∀ z ∈ U, P z = twoPlaneProjection (g.euclideanCoefficients (H z))
        (fderiv ℝ H z 1) (fderiv ℝ H z I)) ∧
      (∀ z ∈ U, 0 < g.inner (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1)) ∧
      MemLp (fun z => fderiv ℝ P z 1) 2 (volume.restrict U) ∧
      MemLp (fun z => fderiv ℝ P z I) 2 (volume.restrict U) := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let G := fun z => g.euclideanCoefficients (H z)
  let P := fun z => twoPlaneProjection (G z)
    (residualRealColumn (Q z)) (residualImagColumn (Q z))
  obtain ⟨hU, hKclosed, hKun, hclosure⟩ := halfDisk_differential_domain hr
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).inter_right
    (isClosed_le continuous_const continuous_im)
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKU : K ⊆ closure U := by rw [hclosure]
  have hGs : ContDiff ℝ 1 g.euclideanCoefficients :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).of_le (by simp)
  have hGK : ContDiffOn ℝ 1 G K := hGs.comp_contDiffOn hH
  have hconfU (z : ℂ) (hz : z ∈ U) :
      G z (fderiv ℝ H z 1) (fderiv ℝ H z I) = 0 ∧
        G z (fderiv ℝ H z I) (fderiv ℝ H z I) =
          G z (fderiv ℝ H z 1) (fderiv ℝ H z 1) := by
    have hh := hconf z (hUK hz)
    dsimp only at hh
    rw [fderivWithin_of_mem_nhds (halfDisk_mem_nhds hz)] at hh
    exact ⟨hh.2, hh.1.symm⟩
  have hfac (z : ℂ) (hz : z ∈ U) :
      complexGradient H z = z ^ m • Q z := by
    have hh := hfactor z (hUK hz)
    simpa only [halfDiskGradient, fderivWithin_of_mem_nhds (halfDisk_mem_nhds hz),
      complexGradient] using hh
  have hzne (z : ℂ) (hz : z ∈ U) : z ≠ 0 := by
    intro he
    have hh : 0 < z.im := hz.2
    simp only [he, zero_im, lt_self_iff_false] at hh
  have hpart (v : ℂ) (hv : v = 1 ∨ v = I) :
      ContinuousOn P K ∧
        (∀ z ∈ U, P z = twoPlaneProjection (G z) (fderiv ℝ H z 1) (fderiv ℝ H z I)) ∧
        MemLp (fun z => fderiv ℝ P z v) 2 (volume.restrict U) := by
    have hDG := compact_within_derivative_memLp hK hKun hU hUK hGK v
    have hDQ : MemLp (fun z => fderiv ℝ Q z v) 2 (volume.restrict (K ∩ U)) := by
      rw [inter_eq_right.mpr hUK]
      exact hv.elim (fun h => h ▸ hDQ1) (fun h => h ▸ hDQI)
    have hh := residual_projection_extension_memLp hK hU hUK hKU hGK.continuousOn
      (hGK.mono hUK) (fun z _ v w => g.symm (H z) v w)
      (fun z _ v hv => g.pos (H z) v hv) hQ hQ1 hQne
      (fun z hz => ⟨z ^ m, pow_ne_zero m (hzne z hz), hfac z hz⟩) hconfU v hDG hDQ
    change ContinuousOn P K ∧
      (∀ z ∈ U, P z = twoPlaneProjection (G z) (fderiv ℝ H z 1) (fderiv ℝ H z I)) ∧
        MemLp (fun z => fderiv ℝ P z v) 2 (volume.restrict (K ∩ U)) at hh
    rwa [inter_eq_right.mpr hUK] at hh
  obtain ⟨hPc, hPeq, hP1⟩ := hpart 1 (Or.inl rfl)
  refine ⟨hPc, hPeq, ?_, hP1, (hpart I (Or.inr rfl)).2.2⟩
  intro z hz
  have hgradne : complexGradient H z ≠ 0 := by
    rw [hfac z hz]
    exact smul_ne_zero (pow_ne_zero m (hzne z hz)) (hQne z (hUK hz))
  obtain ⟨ha, hb⟩ := residual_columns_complexGradient H z
  have hp := residual_columns_factor_pos (G z) (fun v hv => g.pos (H z) v hv) hgradne
    (by simpa only [ha, hb] using (hconfU z hz).2)
  simpa +instances only [ha] using! hp

end PoincareConjecture.M65Branch
