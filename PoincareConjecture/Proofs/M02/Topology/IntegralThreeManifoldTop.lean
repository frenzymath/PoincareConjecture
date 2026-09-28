import PoincareConjecture.Proofs.M02.Topology.IntegralTopCoefficient
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportUniv
import PoincareConjecture.Proofs.M02.Topology.IntegralManifoldOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralManifoldSupport

set_option autoImplicit false

noncomputable section

open Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

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

end PoincareConjecture.Proofs.M02.Topology
