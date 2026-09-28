import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CylinderPeriod
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Deck.Fibers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Deck.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Deck.Transformation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Quotient.Models











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem models_of_terminal_null
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    Nonempty (M27SphereLineFlowCertificate K) ∨
      Nonempty (M27ProjectivePlaneLineFlowCertificate K) ∨
      Nonempty (M27TwistedSphereLineFlowCertificate K) := by
  obtain ⟨c, _, F, q, hs, hc, hl, hm, hscale, hperiod⟩ :=
    K.exists_calibrated_aperiodic_sphereLine_cover_of_terminal_null P x v w hv hw hvw hzero
  apply AncientCylinderQuotient.models_of_fiber_alternatives F q hs hl hm
  apply AncientCylinderDeck.fiber_alternatives q hc _ hperiod
  intro d hd
  let e := AncientCylinderQuotient.deckDiffeomorph q hl d hd
  obtain ⟨L, s, hsign, r, hform⟩ := F.exists_orthogonal_affine_factors hscale e
    (AncientCylinderQuotient.deck_productInner q hl d hd F hm)
  exact ⟨L, s, r, hsign, hform⟩

end PoincareConjecture.AncientKappaSolution
