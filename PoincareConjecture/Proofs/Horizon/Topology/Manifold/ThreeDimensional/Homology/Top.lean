import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralTopCoefficient
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSupportUniv
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralManifoldOrientation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralManifoldSupport








set_option autoImplicit false

noncomputable section

open Set

universe u

namespace Poincare.Topology

theorem nonempty_integralThreeManifoldTop_equiv_int
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [SimplyConnectedSpace M] (x0 : M) :
    Nonempty (integralHomology M 3 ≃ₗ[Int] Int) := by
  obtain ⟨omega, hgen, hlocal⟩ :=
    exists_integralThreeLocallyRepresentedGenerators x0
  obtain ⟨e⟩ := nonempty_integralSupportHomologyUniv_equiv_int x0 3
    (fun K hK => (integralThreeManifoldCompactSupport K hK).2) omega hgen hlocal
  exact ⟨(integralHomologySupportUnivIso M 3).toLinearEquiv.trans e⟩

end Poincare.Topology
