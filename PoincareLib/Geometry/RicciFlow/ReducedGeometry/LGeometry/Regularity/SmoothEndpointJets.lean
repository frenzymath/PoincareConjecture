import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Jets

/-! Reuse the dimension-independent variational declarations adapted from Mapher
`PoincareMT/Proofs/M08/SmoothEndpointJets.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variational
  (endpointJetCutoff
    endpointJetPolynomial
    endpointJetPolynomial_contDiff
    endpointJetPolynomial_deriv
    endpointJetBase
    endpointJetBase_contDiff
    endpointJetBase_hasCompactSupport
    endpointJetBase_eventually_eq
    endpointJetBase_deriv
    exists_small_endpointJet
    exists_smooth_endpoint_jets)

end PoincareMT.LGeometry
