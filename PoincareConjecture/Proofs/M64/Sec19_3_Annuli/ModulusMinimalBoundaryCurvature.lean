import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimalLogCurvature
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusLogBoundaryLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

private theorem modulus_annulus_map_periodic_add (A : M64Annulus g c0 c1)
    (p : LoopPlane) : A.map (annulusPoint curvePeriod 0 + p) = A.map p := by
  have hp : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  have hshift : annulusPoint curvePeriod 0 + p =
      annulusPoint (p 0 + curvePeriod) (p 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint, add_comm]
  rw [hshift, A.periodic, hp]

private theorem modulus_energy_periodic (A : M64Annulus g c0 c1) (r : ℝ)
    (p : LoopPlane)
    (hp : MDifferentiableAt (𝓡 2) (𝓡 n) A.map (annulusPoint curvePeriod 0 + p)) :
    m64ModulusEnergyDensity g r A.map (annulusPoint curvePeriod 0 + p) =
      m64ModulusEnergyDensity g r A.map p := by
  let T : LoopPlane := annulusPoint curvePeriod 0
  have hshift : HasFDerivAt (fun q : LoopPlane => T + q)
      (ContinuousLinearMap.id ℝ LoopPlane) p := (hasFDerivAt_id p).const_add T
  have hfun : (A.map ∘ fun q : LoopPlane => T + q) = A.map :=
    funext (modulus_annulus_map_periodic_add A)
  have hmd : MDifferentiableAt (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) p :=
    hshift.differentiableAt.mdifferentiableAt
  have hd := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 n) p hp hmd
  have hT : mfderiv (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) p =
      ContinuousLinearMap.id ℝ LoopPlane := by
    rw [mfderiv_eq_fderiv]
    exact hshift.fderiv
  rw [hfun, hT] at hd
  have hd' : mfderiv (𝓡 2) (𝓡 n) A.map p =
      mfderiv (𝓡 2) (𝓡 n) A.map (T + p) := by
    simpa only [ContinuousLinearMap.comp_id] using! hd
  have heq : m60AreaGram g A.map (T + p) = m60AreaGram g A.map p := by
    ext i j
    simp only [m60AreaGram, ← hd']
    exact congrArg (fun x : M => g.inner x
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ j)))
      (modulus_annulus_map_periodic_add A p)
  exact congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ =>
    (r * B 0 0 + r⁻¹ * B 1 1) / 2) heq

private theorem modulus_energy_transform_fderiv_periodic
    (A : M64Annulus g c0 c1) (r : ℝ) (Phi : ℝ → ℝ) (p : LoopPlane)
    (hp : ContMDiffAt (𝓡 2) (𝓡 n) ∞ A.map (annulusPoint curvePeriod 0 + p)) :
    fderiv ℝ (fun q => Phi (m64ModulusEnergyDensity g r A.map q))
        (annulusPoint curvePeriod 0 + p) =
      fderiv ℝ (fun q => Phi (m64ModulusEnergyDensity g r A.map q)) p := by
  let T : LoopPlane := annulusPoint curvePeriod 0
  have hnear : ∀ᶠ q in 𝓝 (T + p), ContMDiffAt (𝓡 2) (𝓡 n) 1 A.map q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hp.of_le (by simp))
  have htrans : Tendsto (fun q : LoopPlane => T + q) (𝓝 p) (𝓝 (T + p)) :=
    (continuous_const.add continuous_id).continuousAt.tendsto
  have heq : (fun q => Phi (m64ModulusEnergyDensity g r A.map (T + q))) =ᶠ[𝓝 p]
      fun q => Phi (m64ModulusEnergyDensity g r A.map q) := by
    filter_upwards [htrans.eventually hnear] with q hq
    exact congrArg Phi (modulus_energy_periodic A r q (hq.mdifferentiableAt one_ne_zero))
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_add_left (f := fun q => Phi (m64ModulusEnergyDensity g r A.map q)) T] at hd
  exact hd





theorem m64Annulus_modulusEnergy_fderiv_periodic
    (A : M64Annulus g c0 c1) (r : ℝ) (Phi : ℝ → ℝ) (p : LoopPlane)
    (hp : ContMDiffAt (𝓡 2) (𝓡 n) ∞ A.map (annulusPoint curvePeriod 0 + p)) :
    fderiv ℝ (fun q => Phi (m64ModulusEnergyDensity g r A.map q))
        (annulusPoint curvePeriod 0 + p) =
      fderiv ℝ (fun q => Phi (m64ModulusEnergyDensity g r A.map q)) p :=
  modulus_energy_transform_fderiv_periodic A r Phi p hp

variable [T2Space M] [CompactSpace M]





theorem m64Annulus_modulus_log_energy_boundary_lower_bound
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -2 * K * A.area ≤ r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q + ε))
          (annulusPoint x 1) (EuclideanSpace.single (1 : Fin 2) 1) -
        fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q + ε))
          (annulusPoint x 0) (EuclideanSpace.single (1 : Fin 2) 1) := by
  let E := m64ModulusEnergyDensity g r A.map
  let L := fun q => Real.log (E q + ε)
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hE : ContDiffOn ℝ ∞ E O := m64ModulusEnergyDensity_contDiffOn r hO hA
  have hL : ContDiffOn ℝ ∞ L O := by
    intro p hp
    exact (((hE.contDiffAt (hO.mem_nhds hp)).add contDiffAt_const).log
      (add_pos_of_nonneg_of_pos
        (m64ModulusEnergyDensity_nonneg r hr.le A.map p) hε).ne').contDiffWithinAt
  have hD (b : LoopPlane) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ L q b) O :=
    (hL.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDD (b : LoopPlane) : IntegrableOn
      (fun p => fderiv ℝ (fun q => fderiv ℝ L q b) p b) m64AnnulusDomain volume :=
    (((hD b).fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn.mono hdom
        |>.integrableOn_compact m64AnnulusDomain_isCompact
  have hEI : IntegrableOn E m64AnnulusDomain volume :=
    (hE.continuousOn.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
  have hI : m64AnnulusInterior ⊆ O := m64AnnulusInterior_subset_domain.trans hdom
  have hmem : ∀ᵐ p ∂volume.restrict m64AnnulusDomain, p ∈ m64AnnulusInterior := by
    rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior]
    exact ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet
  have hbound : (∫ p in m64AnnulusDomain, -2 * K * E p) ≤
      ∫ p in m64AnnulusDomain,
        r * fderiv ℝ (fun q => fderiv ℝ L q b0) p b0 +
          r⁻¹ * fderiv ℝ (fun q => fderiv ℝ L q b1) p b1 := by
    apply integral_mono_ae (hEI.const_mul (-2 * K))
      (((hDD b0).const_mul r).add ((hDD b1).const_mul r⁻¹))
    filter_upwards [hmem] with p hp
    exact m64Annulus_modulus_log_energy_laplacian_lower_bound
      D A hr hminimum hconformal (hA.mono hI) hp hK hε (hsec p hp)
  have hseam (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ L (annulusPoint curvePeriod s) b0 = fderiv ℝ L (annulusPoint 0 s) b0 := by
    have hshift : annulusPoint curvePeriod 0 + annulusPoint 0 s =
        annulusPoint curvePeriod s := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    have hp : annulusPoint curvePeriod s ∈ m64AnnulusDomain := by
      change 0 ≤ curvePeriod ∧ curvePeriod ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
      exact ⟨by unfold curvePeriod; positivity, le_rfl, hs⟩
    have hperiod := modulus_energy_transform_fderiv_periodic A r
      (fun v => Real.log (v + ε)) (annulusPoint 0 s)
      (by rw [hshift]; exact hA.contMDiffAt (hO.mem_nhds (hdom hp)))
    rw [hshift] at hperiod
    exact congrArg (fun T : LoopPlane →L[ℝ] ℝ => T b0) hperiod
  have hboundary : (∫ p in m64AnnulusDomain,
        r * fderiv ℝ (fun q => fderiv ℝ L q b0) p b0 +
          r⁻¹ * fderiv ℝ (fun q => fderiv ℝ L q b1) p b1) =
      r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ L (annulusPoint x 1) b1 - fderiv ℝ L (annulusPoint x 0) b1 := by
    rw [integral_add ((hDD b0).const_mul r) ((hDD b1).const_mul r⁻¹),
      integral_const_mul, integral_const_mul, m64Annulus_restrict_closed_eq_interior,
      m64Annulus_integral_horizontal_derivative_of_contDiffOn hO hdom (hD b0),
      m64Annulus_integral_vertical_derivative_of_contDiffOn hO hdom (hD b1)]
    have hzero : (∫ s in Icc (0 : ℝ) 1,
        fderiv ℝ L (annulusPoint curvePeriod s) b0 - fderiv ℝ L (annulusPoint 0 s) b0) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact sub_eq_zero.mpr (hseam s hs)
    rw [hzero, mul_zero, zero_add]
  rw [integral_const_mul, hboundary] at hbound
  have heq : (∫ p in m64AnnulusDomain, E p) = A.area :=
    m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  rw [heq] at hbound
  exact hbound





theorem m64Annulus_modulus_log_boundary_curvature_le
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m64ModulusEnergyDensity g r A.map (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m64ModulusEnergyDensity g r A.map (annulusPoint x 1)) :
    -(1 / 2 : ℝ) * r⁻¹ *
      ((∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ (m64ModulusEnergyDensity g r A.map) (annulusPoint x 1)
            (EuclideanSpace.single (1 : Fin 2) 1) /
          m64ModulusEnergyDensity g r A.map (annulusPoint x 1)) -
        ∫ x in Icc (0 : ℝ) curvePeriod,
          fderiv ℝ (m64ModulusEnergyDensity g r A.map) (annulusPoint x 0)
              (EuclideanSpace.single (1 : Fin 2) 1) /
            m64ModulusEnergyDensity g r A.map (annulusPoint x 0)) ≤ K * A.area := by
  let E := m64ModulusEnergyDensity g r A.map
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hE : ContDiffOn ℝ ∞ E O := m64ModulusEnergyDensity_contDiffOn r hO hA
  have hlo := m64Annulus_log_normal_trace_tendsto hO hdom hE
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hlower
  have hhi := m64Annulus_log_normal_trace_tendsto hO hdom hE
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hupper
  have hbound : -2 * K * A.area ≤ r⁻¹ *
      ((∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 1) b1 /
        E (annulusPoint x 1)) -
      ∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 0) b1 /
        E (annulusPoint x 0)) := by
    apply ge_of_tendsto ((hhi.sub hlo).const_mul r⁻¹)
    apply Eventually.of_forall
    intro m
    let eps : ℝ := 1 / ((m : ℝ) + 1)
    have heps : 0 < eps := by dsimp only [eps]; positivity
    let L := fun p => Real.log (E p + eps)
    have hL : ContDiffOn ℝ ∞ L O := by
      intro p hp
      exact (((hE.contDiffAt (hO.mem_nhds hp)).add contDiffAt_const).log
        (add_pos_of_nonneg_of_pos
          (m64ModulusEnergyDensity_nonneg r hr.le A.map p) heps).ne').contDiffWithinAt
    have hD : ContinuousOn (fun p => fderiv ℝ L p b1) O :=
      ((hL.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
    have htrace (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        IntegrableOn (fun x => fderiv ℝ L (annulusPoint x s) b1)
          (Icc (0 : ℝ) curvePeriod) volume := by
      have hcurve : Continuous (fun x : ℝ => annulusPoint x s) := by
        unfold annulusPoint
        fun_prop
      apply (hD.comp hcurve.continuousOn ?_).integrableOn_compact isCompact_Icc
      intro x hx
      apply hdom
      change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
      exact ⟨hx.1, hx.2, hs⟩
    have hraw := m64Annulus_modulus_log_energy_boundary_lower_bound
      D A hr hminimum hconformal hO hdom hA hK heps hsec
    change -2 * K * A.area ≤ r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ L (annulusPoint x 1) b1 - fderiv ℝ L (annulusPoint x 0) b1 at hraw
    rw [integral_sub (htrace 1 (by simp)) (htrace 0 (by simp))] at hraw
    exact hraw
  change -(1 / 2 : ℝ) * r⁻¹ *
    ((∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 1) b1 /
      E (annulusPoint x 1)) -
    ∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 0) b1 /
      E (annulusPoint x 0)) ≤ K * A.area
  linarith

end PoincareConjecture
