import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.TensorTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.AmbientTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CenteredPositivity

/-!
# Positive sectional curvature of a round component

The fixed tolerance in the original round comparison bounds the actual
covariant metric two-jet. Normal coordinates and the quantitative curvature
estimate give positivity, which transports back through the original
comparison map and its positive metric scale.
Source: Morgan--Tian, Definition 9.75, pp. 230-231.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.SingularRoundComponent

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)

theorem positive_sectional (D : LeviCivitaData g) (hepsilon : epsilon ≤ 1 / 200)
    (x : M) (hx : x ∈ N.carrier) (v w : TangentSpace (𝓡 3) x)
    (hpair : LeviCivitaData.IsOrthonormalPair g x v w) :
    0 < D.sectionalCurvature x v w := by
  have hx' : x ∈ range N.forward := N.forward_image.symm ▸ hx
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨e, g₀, h, D₀, Dh, U, hU, h0, hUse, hep, he, _hei, _hinv,
    _hg₀, hh, hzero, hΓ, hjet, hcurv⟩ := N.exists_normalCoordinateRealization hepsilon p
  subst p
  apply N.sectionalCurvature_pos_of_coordinate_realization D e Dh hU h0
    (he.mono hUse) hh ?_ v w hpair
  intro a b hlin
  exact D₀.curvatureTensor_pos_of_centered_round_twoJet Dh 0 N.epsilon_pos.le
    hepsilon hzero hΓ hjet (fun u z hu hz huz => hcurv u z ⟨hu, hz, huz⟩) a b hlin

end PoincareMT.SingularRoundComponent
