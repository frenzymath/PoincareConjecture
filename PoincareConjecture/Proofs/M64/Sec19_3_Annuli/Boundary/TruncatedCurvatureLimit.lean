import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.TruncatedLogCurvature

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

theorem annulus_slice_log_shift_tendsto {a : LoopPlane → ℝ}
    (ha : ContDiffOn ℝ ∞ a m64AnnulusOpenStrip) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpos : ∀ x ∈ Icc (0 : ℝ) curvePeriod, 0 < a (annulusPoint x s)) :
    Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..curvePeriod,
      fderiv ℝ (fun q => Real.log (a q + 1 / ((m : ℝ) + 1)))
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1)) atTop
      (𝓝 (∫ x in (0 : ℝ)..curvePeriod,
        fderiv ℝ (fun q => Real.log (a q)) (annulusPoint x s)
          (EuclideanSpace.single (1 : Fin 2) 1))) := by
  have hp (x : ℝ) : annulusPoint x s ∈ m64AnnulusOpenStrip := hs
  have hP : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  have hlim := m64Annulus_log_normal_trace_tendsto_on_slice
    isOpen_m64AnnulusOpenStrip ha s (fun x _ => hp x) hpos
  have heq : (∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ a (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) /
        a (annulusPoint x s)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ (fun q => Real.log (a q)) (annulusPoint x s)
          (EuclideanSpace.single (1 : Fin 2) 1) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    have hd := (ha.contDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds (hp x))).differentiableAt
      (by simp)
    dsimp only
    rw [(hd.hasFDerivAt.log (hpos x hx).ne').fderiv]
    simp only [smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq] at hlim
  simpa only [intervalIntegral.integral_of_le hP, integral_Icc_eq_integral_Ioc] using hlim

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem annulus_truncated_log_curvature_le
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    {lo hi K : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) (hhi : hi < 1) (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (hposlo : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m64ModulusEnergyDensity g r A.map (annulusPoint x lo))
    (hposhi : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m64ModulusEnergyDensity g r A.map (annulusPoint x hi)) :
    -(1 / 2 : ℝ) * r⁻¹ *
      ((∫ x in (0 : ℝ)..curvePeriod,
        fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q))
          (annulusPoint x hi) (EuclideanSpace.single (1 : Fin 2) 1)) -
        ∫ x in (0 : ℝ)..curvePeriod,
          fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q))
            (annulusPoint x lo) (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K * A.area := by
  have hE := m64ModulusEnergyDensity_contDiffOn (g := g) r isOpen_m64AnnulusOpenStrip hA
  have hL := annulus_slice_log_shift_tendsto hE ⟨hlo, hlh.trans_lt hhi⟩ hposlo
  have hU := annulus_slice_log_shift_tendsto hE ⟨hlo.trans_le hlh, hhi⟩ hposhi
  have hbound := ge_of_tendsto ((hU.sub hL).const_mul r⁻¹)
    (Eventually.of_forall (fun m : ℕ =>
      annulus_truncated_log_energy_lower_bound D A hr hminimum hconformal hA
        hlo hlh hhi hK (show 0 < 1 / ((m : ℝ) + 1) by positivity) hsec))
  linarith

end PoincareConjecture.M64
