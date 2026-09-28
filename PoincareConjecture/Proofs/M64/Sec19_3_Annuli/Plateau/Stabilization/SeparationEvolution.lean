import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FiniteRampForward
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.AreaConvergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.LeastAreaContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ForwardPointwiseLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CurvatureSupremum

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_ramp_evolution
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (hramp0 : ∀ t ∈ Ioo a b, M63IsRampAt P (fun x ↦ c0 x t) t)
    (hramp1 : ∀ t ∈ Ioo a b, M63IsRampAt P (fun x ↦ c1 x t) t)
    (A0 : M64Annulus (P.flow.metric a) (fun x ↦ c0 x a) (fun x ↦ c1 x a))
    {K0 K1 K2 : ℝ} (hK0 : 0 ≤ K0) (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    (∀ t ∈ Ico a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * m64FlowAnnulusArea P c0 c1 t) t) ∧
    (∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      m64FlowAnnulusArea P c0 c1 t ≤
        Real.exp ((2 * (n : ℝ) - 1) * K0 * (t - s)) * m64FlowAnnulusArea P c0 c1 s) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let d0 := fun x s ↦ auxiliaryCircleSection Q (Q.circle.quotient 0) (c0 x s)
  let d1 := fun delta x s ↦ auxiliaryCircleSection Q (Q.circle.quotient delta) (c1 x s)
  let mu := fun delta ↦ m64FlowAnnulusArea Q d0 (d1 delta)
  let k := fun t ↦ (2 * (n : ℝ) - 1) * m64CurvatureSupremum F t
  let rate := (2 * (n : ℝ) - 1) * K0
  have hnonempty := m64AnnulusFlow_nonempty_of_initial isCompact_univ
    P.circle.positive P hc0 hc1 A0
  have hcontinuous := m64AnnulusFlow_continuous_of_initial isCompact_univ
    P.circle.positive P hc0 hc1 A0
  have hlimit (t : ℝ) (ht : t ∈ Icc a b) :
      Tendsto (fun delta ↦ mu delta t) (𝓝[>] 0) (𝓝 (m64FlowAnnulusArea P c0 c1 t)) := by
    obtain ⟨A⟩ := hnonempty t ht
    exact (auxiliaryCircle_lifted_leastArea_tendsto Q t A).mono_left nhdsWithin_le_nhds
  have hd0 : M63C2ShrinkingCurveOn Q.flow d0 (Icc a b) :=
    auxiliaryCircle_c2ShrinkingCurve Q (Q.circle.quotient 0) hc0
  have hd1 (delta : ℝ) : M63C2ShrinkingCurveOn Q.flow (d1 delta) (Icc a b) :=
    auxiliaryCircle_c2ShrinkingCurve Q (Q.circle.quotient delta) hc1
  have hdata : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      ContinuousOn (mu delta) (Icc a b) ∧
      (∀ t ∈ Icc a b, 0 ≤ mu delta t) ∧
      ∀ t ∈ Ioo a b,
        AnnulusForwardDerivativeBound (mu delta) (k t * mu delta t) t ∧
        AnnulusForwardDerivativeBound (mu delta) (rate * mu delta t) t := by
    filter_upwards [Ioo_mem_nhdsGT Q.circle.positive] with delta hdelta
    obtain ⟨B0, -⟩ := auxiliaryCircle_radial_annulus Q a A0 delta
    refine ⟨m64AnnulusFlow_continuous_of_initial isCompact_univ Q.circle.positive Q
      hd0 (hd1 delta) B0,
      m64AnnulusFlow_nonnegative_of_initial isCompact_univ Q.circle.positive Q
        hd0 (hd1 delta) B0, ?_⟩
    intro t ht
    obtain ⟨A⟩ := hnonempty t (Ioo_subset_Icc_self ht)
    have hforward := auxiliaryCircle_ramp_forward P Q hn hc0 hc1 ht
      (hramp0 t ht) (hramp1 t ht) A hdelta.1 hdelta.2
    have hbounded := m64CurvatureRange_bddAbove_of_compact
      (F := F) isCompact_univ (Ioo_subset_Icc_self ht)
    exact ⟨hforward.1 (m64CurvatureSupremum F t) (m64CurvatureSupremum_nonneg hbounded)
      (m64Curvature_le_supremum hbounded), hforward.2 K0 K1 K2 hK0 hBounds⟩
  constructor
  · exact m64AnnulusForwardDerivativeBound.of_pointwise_limit hcontinuous
      (continuousOn_const.mul (m64CurvatureSupremum_continuous_of_compact isCompact_univ))
      (hdata.mono (fun _ hd ↦ ⟨hd.1, hd.2.1, fun t ht ↦ (hd.2.2 t ht).1⟩)) hlimit
  · intro s t hs ht hst
    exact m64AnnulusForwardDerivativeBound.exponential_comparison_of_pointwise_limit
      (k := fun _ ↦ rate)
      (hdata.mono (fun _ hd ↦ ⟨hd.1, hd.2.1, fun x hx ↦ (hd.2.2 x hx).2⟩))
      hlimit hs ht hst (fun _ _ ↦ le_rfl)

end PoincareConjecture.M64
