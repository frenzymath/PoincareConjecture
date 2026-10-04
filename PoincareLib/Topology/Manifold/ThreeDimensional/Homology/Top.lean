import PoincareLib.AlgebraicTopology.SingularHomology.Chains.IntegralTopCoefficient
import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralSupportUniv
import PoincareLib.AlgebraicTopology.SingularHomology.Orientation.IntegralManifoldOrientation
import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralManifoldSupport

/-!
# Top integral homology of a compact simply connected three-manifold

The local orientation covering supplies coherent generators. Compact support
gluing and point detection identify the coefficient of each global class,
and the pair with empty subspace identifies supported and absolute homology.
-/

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
