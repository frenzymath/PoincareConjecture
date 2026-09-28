import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteCurrentDivergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteModulusDivergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMetricDerivative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteRicciTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionEnergyIntegral

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {d : ℕ} {c0 c1 : ℝ → M}

theorem m64ParameterAnnulus_boundary_first_variation
    (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (A : M64Annulus (F.metric t) c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
      m60AreaGram (F.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hTF : ∀ s ∈ Ioo (-epsilon) epsilon, t + s ∈ Ioo a b)
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    {Phi : ℝ × EuclideanSpace ℝ (Fin d) → M}
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin d)) (𝓡 n) ∞ Phi
      (Ioo (-epsilon) epsilon ×ˢ O))
    {h : LoopPlane → EuclideanSpace ℝ (Fin d)}
    (hh : ContDiffOn ℝ 1 h m64AnnulusDomain) (hmap : MapsTo h m64AnnulusDomain O)
    (hbase : ∀ p, Phi (0, h p) = A.map p) :
    let v := fun s p => Phi (s, h p)
    let J0 := fun p => r * m64FiniteAnnulusCurrent (F.metric t) v 0 p
    let J1 := fun p => r⁻¹ * m64FiniteAnnulusCurrent (F.metric t) v 1 p
    let R := fun p =>
      r * (F.connection t).ricci (v 0 p)
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      r⁻¹ * (F.connection t).ricci (v 0 p)
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
        m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p)
      (((∫ x in Icc (0 : ℝ) curvePeriod, J1 (annulusPoint x 1)) -
          ∫ x in Icc (0 : ℝ) curvePeriod, J1 (annulusPoint x 0)) +
        ((∫ y in Icc (0 : ℝ) 1, J0 (annulusPoint curvePeriod y)) -
          ∫ y in Icc (0 : ℝ) 1, J0 (annulusPoint 0 y)) -
        ∫ p in m64AnnulusDomain, R p) 0 := by
  let v := fun s p => Phi (s, h p)
  let J := m64FiniteAnnulusCurrent (F.metric t) v
  let J0 := fun p => r * J 0 p
  let J1 := fun p => r⁻¹ * J 1 p
  let R := fun p =>
    r * (F.connection t).ricci (v 0 p)
      (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
    r⁻¹ * (F.connection t).ricci (v 0 p)
      (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
      (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  let E := fun s p => m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p
  let Q := fun p => fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
    fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hopen : IsOpen (Ioo (-epsilon) epsilon ×ˢ O) := isOpen_Ioo.prod hO
  have hsub : m64AnnulusInterior ⊆ interior m64AnnulusDomain :=
    interior_maximal m64AnnulusInterior_subset_domain isOpen_m64AnnulusInterior
  have hv0 : ContMDiffOn (𝓡 2) (𝓡 n) 1 (v 0) m64AnnulusDomain :=
    (hPhi.of_le (by simp)).comp (contDiffOn_const.prodMk hh).contMDiffOn
      (fun p hp => ⟨hzero, hmap hp⟩)
  have hvint : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (v 0) m64AnnulusInterior := by
    change ContMDiffOn (𝓡 2) (𝓡 n) ∞ (fun p => Phi (0, h p)) m64AnnulusInterior
    rw [funext hbase]
    exact hA
  have hV := m64ParameterAnnulus_timeVelocity_contMDiffOn isOpen_Ioo hO hPhi hh hmap hzero
  have hc (i : Fin 2) : ContinuousOn (J i) m64AnnulusDomain :=
    m64FiniteAnnulusCurrent_continuousOn (F.metric t) hv0 hV.continuousOn i
  have hdiff (i : Fin 2) (p : LoopPlane) (hp : p ∈ m64AnnulusInterior) :
      DifferentiableAt ℝ (J i) p :=
    m64FiniteAnnulusCurrent_differentiableAt (F.metric t) (hsub hp)
      (hvint.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp))
      (hV.contMDiffAt (mem_interior_iff_mem_nhds.mp (hsub hp))) i
  have hR : IntegrableOn R m64AnnulusDomain volume :=
    m64Annulus_modulusRicci_integrable (F.connection t) r hv0
  obtain ⟨hE, hd⟩ := m64AnnulusMotionEnergy_hasDerivAt F t hepsilon hTF hO Phi
    (by simpa +instances only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using! hPhi)
    r hh.contMDiffOn hmap
  have hpoint (p : LoopPlane) (hp : p ∈ m64AnnulusInterior) :
      deriv (fun s => E s p) 0 + R p = Q p := by
    have hcoords : annulusPoint (p 0) (p 1) = p := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    have hdiv := m64ParameterAnnulus_modulusEnergyDensity_eq_current_divergence
      (F.connection t) A hr hminimum hconformal hA hopen hPhi hh hbase
      (x := p 0) (s := p 1)
      (by rw [hcoords]; exact ⟨hzero, hmap (m64AnnulusInterior_subset_domain hp)⟩)
      (by rw [hcoords]; exact hp)
    have htime := m64ParameterAnnulus_moving_metric_energy_hasDerivAt F r ht hopen hPhi
      ((hh.contDiffAt (mem_interior_iff_mem_nhds.mp (hsub hp))).differentiableAt one_ne_zero)
      (show (0, h p) ∈ Ioo (-epsilon) epsilon ×ˢ O from
        ⟨hzero, hmap (m64AnnulusInterior_subset_domain hp)⟩)
    dsimp only at hdiv htime
    simp only [hcoords] at hdiv
    dsimp only [E, Q, J0, J1, R]
    rw [htime.deriv, fderiv_const_mul (hdiff 0 p hp), fderiv_const_mul (hdiff 1 p hp)]
    simp only [smul_apply, smul_eq_mul, EuclideanSpace.basisFun_apply]
    dsimp only [J, v] at *
    linarith only [hdiv]
  have hae : (fun p => deriv (fun s => E s p) 0 + R p) =ᵐ[volume.restrict m64AnnulusDomain] Q := by
    rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior]
    filter_upwards [ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet] with p hp
    exact hpoint p hp
  have hQ : IntegrableOn Q m64AnnulusDomain volume := (hE.add hR).congr hae
  have hboundary := m64Annulus_integral_divergence_of_continuous
    ((hc 0).const_mul r) ((hc 1).const_mul r⁻¹)
    (fun p hp => (hdiff 0 p hp).const_mul r)
    (fun p hp => (hdiff 1 p hp).const_mul r⁻¹) hQ
  apply hd.congr_deriv
  have heq := integral_congr_ae hae
  rw [integral_add hE hR] at heq
  change (∫ p in m64AnnulusDomain, deriv (fun s => E s p) 0) = _
  rw [← hboundary]
  linarith only [heq]

end PoincareConjecture
