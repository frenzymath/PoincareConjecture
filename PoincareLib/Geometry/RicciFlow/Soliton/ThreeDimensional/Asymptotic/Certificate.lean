import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Models

/-!
# Three-dimensional asymptotic classification certificate

The declaration is unchanged from Mapher's M20 definitions at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`. It retains the specified
sequence, its M18 limit, and equality with the classified entire flow.
Morgan--Tian, Corollaries 9.53--9.54, pp. 217--218.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure ThreeDimensionalAsymptoticClassificationCertificate
    {K : AncientKappaSolution 3 M} (S : AncientRescalingSequence K)
    (L : AncientAsymptoticSolitonLimitData S) where
  bounded_curvature :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : C.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B
  classified_flow :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
    letI : Nonempty C.carrier := ⟨Classical.choose C.connected.nonempty⟩
    letI : ConnectedSpace C.carrier := ⟨inferInstance⟩
    ∃ (S₀ : GradientShrinkingSolitonData 3 C.carrier)
      (G : ShrinkingSolitonFlow S₀),
      S₀.metric = L.convergence.limit.flow.metric (-1) ∧
      G.flow = L.convergence.limit.flow ∧
      Nonempty (ThreeDimensionalSolitonModel S₀ G)

end PoincareMT
