import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RadialRectangleDivergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimalBoundaryCurvature







noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem annulus_truncated_log_energy_lower_bound
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    {lo hi K eps : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) (hhi : hi < 1)
    (hK : 0 ≤ K) (heps : 0 < eps)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -2 * K * A.area ≤ r⁻¹ *
      ((∫ x in (0 : ℝ)..curvePeriod,
        fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q + eps))
          (annulusPoint x hi) (EuclideanSpace.single (1 : Fin 2) 1)) -
        ∫ x in (0 : ℝ)..curvePeriod,
          fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q + eps))
            (annulusPoint x lo) (EuclideanSpace.single (1 : Fin 2) 1)) := by
  let E := m64ModulusEnergyDensity g r A.map
  let L := fun q => Real.log (E q + eps)
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let R := annulusRadialRectangle lo hi
  have hO := isOpen_m64AnnulusOpenStrip
  have hsub : R ⊆ m64AnnulusDomain := annulusRadialRectangle_subset hlo.le hhi.le
  have hstrip : R ⊆ m64AnnulusOpenStrip := annulusRadialRectangle_subset_strip hlo hhi
  have hE : ContDiffOn ℝ ∞ E m64AnnulusOpenStrip :=
    m64ModulusEnergyDensity_contDiffOn r hO hA
  have hL : ContDiffOn ℝ ∞ L m64AnnulusOpenStrip := by
    intro p hp
    exact (((hE.contDiffAt (hO.mem_nhds hp)).add contDiffAt_const).log
      (add_pos_of_nonneg_of_pos
        (m64ModulusEnergyDensity_nonneg r hr.le A.map p) heps).ne').contDiffWithinAt
  have hD (b : LoopPlane) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ L q b)
      m64AnnulusOpenStrip :=
    (hL.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDD (b : LoopPlane) : IntegrableOn
      (fun p => fderiv ℝ (fun q => fderiv ℝ L q b) p b) R volume :=
    ((((hD b).fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn.mono hstrip).integrableOn_compact
        (annulusRadialRectangle_isCompact lo hi)
  have hEI : IntegrableOn E m64AnnulusDomain volume :=
    m64_weightedGram_integrable_of_ae_modulus_conformal A hr hconformal
  have hmem : ∀ᵐ p ∂volume.restrict R, p ∈ m64AnnulusInterior := by
    apply ae_restrict_of_ae_restrict_of_subset hsub
    rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior]
    exact ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet
  have hbound : (∫ p in R, -2 * K * E p) ≤ ∫ p in R,
      r * fderiv ℝ (fun q => fderiv ℝ L q b0) p b0 +
        r⁻¹ * fderiv ℝ (fun q => fderiv ℝ L q b1) p b1 := by
    apply integral_mono_ae ((hEI.mono_set hsub).const_mul (-2 * K))
      (((hDD b0).const_mul r).add ((hDD b1).const_mul r⁻¹))
    filter_upwards [hmem] with p hp
    exact m64Annulus_modulus_log_energy_laplacian_lower_bound D A hr hminimum
      hconformal (hA.mono (fun _ h => h 1 (mem_univ _))) hp hK heps (hsec p hp)
  have harea : (∫ p in R, E p) ≤ A.area := by
    rw [← m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal]
    exact setIntegral_mono_set hEI
      (Eventually.of_forall (fun p => m64ModulusEnergyDensity_nonneg r hr.le A.map p))
      (Eventually.of_forall hsub)
  have hseam (s : ℝ) (hs : s ∈ Icc lo hi) :
      r * fderiv ℝ L (annulusPoint curvePeriod s) b0 =
        r * fderiv ℝ L (annulusPoint 0 s) b0 := by
    have hshift : annulusPoint curvePeriod 0 + annulusPoint 0 s =
        annulusPoint curvePeriod s := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    have hp : annulusPoint curvePeriod s ∈ m64AnnulusOpenStrip :=
      ⟨hlo.trans_le hs.1, hs.2.trans_lt hhi⟩
    have hd := m64Annulus_modulusEnergy_fderiv_periodic A r
      (fun v => Real.log (v + eps)) (annulusPoint 0 s)
      (by rw [hshift]; exact hA.contMDiffAt (hO.mem_nhds hp))
    rw [hshift] at hd
    exact congrArg (fun T : LoopPlane →L[ℝ] ℝ => r * T b0) hd
  have hdiv := annulusRadialRectangle_integral_divergence_periodic hlh hO hstrip
    (J1 := fun q => r⁻¹ * fderiv ℝ L q b1)
    ((contDiffOn_const.mul (hD b0)).of_le (by simp))
    ((contDiffOn_const.mul (hD b1)).of_le (by simp)) hseam
  have hder (c : ℝ) (b : LoopPlane) (p : LoopPlane) (hp : p ∈ R) :
      fderiv ℝ (fun q => c * fderiv ℝ L q b) p b =
        c * fderiv ℝ (fun q => fderiv ℝ L q b) p b := by
    have hd := ((hD b).contDiffAt (hO.mem_nhds (hstrip hp))).differentiableAt (by simp)
    rw [(hd.hasFDerivAt.const_mul c).fderiv]
    rfl
  have hleft : (∫ p in R,
      fderiv ℝ (fun q => r * fderiv ℝ L q b0) p b0 +
        fderiv ℝ (fun q => r⁻¹ * fderiv ℝ L q b1) p b1) =
      ∫ p in R, r * fderiv ℝ (fun q => fderiv ℝ L q b0) p b0 +
        r⁻¹ * fderiv ℝ (fun q => fderiv ℝ L q b1) p b1 := by
    apply setIntegral_congr_fun (annulusRadialRectangle_isCompact lo hi).measurableSet
    intro p hp
    dsimp only
    rw [hder r b0 p hp, hder r⁻¹ b1 p hp]
  rw [hleft, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← mul_sub] at hdiv
  rw [integral_const_mul, hdiv] at hbound
  exact (mul_le_mul_of_nonpos_left harea (by nlinarith : -2 * K ≤ 0)).trans hbound

end PoincareConjecture.M64
