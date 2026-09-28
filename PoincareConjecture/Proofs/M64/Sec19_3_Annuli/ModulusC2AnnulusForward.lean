import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusProductAnnulusVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusBoundaryRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusC2BoundaryMotion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64CircleProductAnnulus_modulus_exists_forward_of_c2_curves
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b)
    (A : M64Annulus (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  have hct0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ (fun x => c0 x t) := by
    simpa only [A.lower_boundary] using
      m64Annulus_slice_contMDiff A hO hdom hA (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hct1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ (fun x => c1 x t) := by
    simpa only [A.upper_boundary] using
      m64Annulus_slice_contMDiff A hO hdom hA (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  obtain ⟨epsilon0, hepsilon0, f0, hf0, hp0, ha0, hv0⟩ :=
    m64C2ShrinkingCurve_exists_centered_motion_of_smooth_slice P.flow hc0 ht hct0
  obtain ⟨epsilon1, hepsilon1, f1, hf1, hp1, ha1, hv1⟩ :=
    m64C2ShrinkingCurve_exists_centered_motion_of_smooth_slice P.flow hc1 ht hct1
  let epsilon := min epsilon0 epsilon1
  have hepsilon : 0 < epsilon := lt_min hepsilon0 hepsilon1
  have hsub0 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsub1 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon1) epsilon1 :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hinit0 (x : ℝ) : f0 0 x = c0 x t := by
    simpa only [add_zero] using ha0 0 (hsub0 hzero) x
  have hinit1 (x : ℝ) : f1 0 x = c1 x t := by
    simpa only [add_zero] using ha1 0 (hsub1 hzero) x
  have hpoint {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod)
      (hs : s ∈ Icc (0 : ℝ) 1) : annulusPoint x s ∈ m64AnnulusDomain := by
    change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
    exact ⟨hx.1, hx.2, hs⟩
  have hlower (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      0 < m64ModulusEnergyDensity (P.flow.metric t) r A.map (annulusPoint x 0) := by
    apply m64Annulus_modulusEnergyDensity_pos_of_horizontal_immersed (P.flow.metric t) hr
      ((hA.contMDiffAt (hO.mem_nhds (hdom (hpoint hx (by simp))))).mdifferentiableAt
        (by simp))
    have heq : (fun y => A.map (annulusPoint y 0)) = (fun y => c0 y t) :=
      funext A.lower_boundary
    rw [heq]
    exact hc0.immersed t (Ioo_subset_Icc_self ht) x
  have hupper (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      0 < m64ModulusEnergyDensity (P.flow.metric t) r A.map (annulusPoint x 1) := by
    apply m64Annulus_modulusEnergyDensity_pos_of_horizontal_immersed (P.flow.metric t) hr
      ((hA.contMDiffAt (hO.mem_nhds (hdom (hpoint hx (by simp))))).mdifferentiableAt
        (by simp))
    have heq : (fun y => A.map (annulusPoint y 1)) = (fun y => c1 y t) :=
      funext A.upper_boundary
    rw [heq]
    exact hc1.immersed t (Ioo_subset_Icc_self ht) x
  obtain ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, hlo, hup, hadmit⟩ :=
    m64Annulus_exists_smooth_moving_boundary_family A hO hdom hA hepsilon
      f0 f1 (hf0.mono (prod_mono_left hsub0)) (hf1.mono (prod_mono_left hsub1))
      hinit0 hinit1 hp0 hp1
  have hvelocity0 (x : ℝ) : curveVelocity (fun z => v (z, annulusPoint x 0)) 0 =
      m62CurvatureVector P.flow (fun y _ => c0 y t) t x :=
    (congrArg (fun f : ℝ → P.charts.Point => curveVelocity (n := n + 1) f 0)
      (funext (fun z => hlo z x))).trans (hv0 x)
  have hvelocity1 (x : ℝ) : curveVelocity (fun z => v (z, annulusPoint x 1)) 0 =
      m62CurvatureVector P.flow (fun y _ => c1 y t) t x :=
    (congrArg (fun f : ℝ → P.charts.Point => curveVelocity (n := n + 1) f 0)
      (funext (fun z => hup z x))).trans (hv1 x)
  have hforward := (m64CircleProductAnnulus_modulus_sharp_variation P hn hcirc ht
    A hr hminimum hconformal hO hdom hA hK hcurv hlower hupper
    hdelta hU hDU hv hbase hperiodic hvelocity0 hvelocity1).2
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-delta) delta :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hdelta⟩)
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon) epsilon :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hzero)
  intro eta heta
  filter_upwards [hforward eta heta, hsmall, htime] with h hh hδ he
  obtain ⟨B, hB⟩ := hadmit h hδ (P.flow.metric (t + h))
  have harea : B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
    change m64AnnulusArea (P.flow.metric (t + h)) B.map ≤ _
    rw [hB]
    exact hh
  have he0 : f0 h = (fun x => c0 x (t + h)) := funext (ha0 h (hsub0 he))
  have he1 : f1 h = (fun x => c1 x (t + h)) := funext (ha1 h (hsub1 he))
  exact he0 ▸ he1 ▸ ⟨B, harea⟩

theorem m64CircleProductAnnulus_modulus_exists_forward_with_curvature_supremum
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b)
    (A : M64Annulus (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area +
          h * ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * A.area + eta) := by
  have hbounded := m64CurvatureRange_bddAbove_of_compact
    (F := F) isCompact_univ (Ioo_subset_Icc_self ht)
  exact m64CircleProductAnnulus_modulus_exists_forward_of_c2_curves P hn hcirc hc0 hc1 ht
    A hr hminimum hconformal hO hdom hA (m64CurvatureSupremum_nonneg hbounded)
    (m64Curvature_le_supremum hbounded)

end PoincareConjecture
