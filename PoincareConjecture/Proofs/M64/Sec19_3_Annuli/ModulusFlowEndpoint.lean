import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusForwardEndpoint
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CurvatureSupremum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.LeastAreaContinuity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64AnnulusFlow_forward_on_Ico_of_on_Ioo
    (hcompact : IsCompact (univ : Set M)) (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a))
    (hforward : ∀ t ∈ Ioo a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64FlowAnnulusArea P c0 c1 t) t) :
    ∀ t ∈ Ico a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64FlowAnnulusArea P c0 c1 t) t := by
  have hf := m64AnnulusFlow_continuous_of_initial hcompact hcirc P hc0 hc1 A
  have hq : ContinuousOn
      (fun t => (2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
        m64FlowAnnulusArea P c0 c1 t) (Icc a b) :=
    (continuousOn_const.mul (m64CurvatureSupremum_continuous_of_compact hcompact)).mul hf
  exact m64AnnulusForwardDerivativeBound.on_Ico_of_on_Ioo hf hq hforward

end PoincareConjecture
