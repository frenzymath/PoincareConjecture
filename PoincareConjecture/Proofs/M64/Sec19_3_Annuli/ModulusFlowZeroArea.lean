import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFlowEndpoint
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusZeroAreaForward













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64AnnulusFlow_forward_on_Ico_of_positive_on_Ioo
    (hcompact : IsCompact (univ : Set M)) (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a))
    (hforward : ∀ t ∈ Ioo a b, 0 < m64FlowAnnulusArea P c0 c1 t →
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64FlowAnnulusArea P c0 c1 t) t) :
    ∀ t ∈ Ico a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64FlowAnnulusArea P c0 c1 t) t := by
  exact m64AnnulusForwardDerivativeBound.on_Ico_of_positive_on_Ioo
    (m64AnnulusFlow_continuous_of_initial hcompact hcirc P hc0 hc1 A)
    (continuousOn_const.mul (m64CurvatureSupremum_continuous_of_compact hcompact))
    (m64AnnulusFlow_nonnegative_of_initial hcompact hcirc P hc0 hc1 A) hforward





theorem m64AnnulusFlow_exponential_of_positive_forward
    (hcompact : IsCompact (univ : Set M)) (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a))
    {K : ℝ} (hK : 0 ≤ K)
    (hforward : ∀ t ∈ Ioo a b, 0 < m64FlowAnnulusArea P c0 c1 t →
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        (K * m64FlowAnnulusArea P c0 c1 t) t) :
    ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      m64FlowAnnulusArea P c0 c1 t ≤
        Real.exp (K * (t - s)) * m64FlowAnnulusArea P c0 c1 s := by
  have hf := m64AnnulusFlow_continuous_of_initial hcompact hcirc P hc0 hc1 A
  have hn := m64AnnulusFlow_nonnegative_of_initial hcompact hcirc P hc0 hc1 A
  intro s t hs ht hst
  exact m64AnnulusForwardDerivativeBound.exponential_of_positive_on_Ioo hK
    (hf.mono (Icc_subset_Icc hs.1 ht.2)) (hn s hs)
    (fun x hx => hforward x ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩)
    t ⟨hst, le_rfl⟩

end PoincareConjecture
