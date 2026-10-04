import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Neck.CanonicalNeckModelFrame
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Neck.CanonicalNeckTipRealization
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Neck.CanonicalNeckTipIsotropy
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureNativeBounds
import PoincareLib.Geometry.Riemannian.Connection.ChangeMetric

/-!
# The rotational tip is excluded at the frozen native accuracy

Every actual tensor input is supplied by the original native comparison
at its actual coordinate point. There is no further accuracy choice.
Claim 17.2, pp. 399-401; canonical-neck-native-tip.md, C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.Proofs.M47

open PoincareMT.M47

/-- The actual rotational tip cannot lie in the full original fine neck. -/
theorem standardNeck_tip_not_mem
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {epsilon : ℝ} (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200)
    {center : StandardCapSpace} (N : StandardCylinderPatch epsilon⁻¹ center)
    (hclose : RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate)) :
    (0 : StandardCapSpace) ∉ N.carrier := by
  intro htip
  obtain ⟨⟨q, s⟩, hs, htip⟩ := N.coordinate_image.symm ▸ htip
  obtain ⟨g1, D1, W, hW, hpW, hcoeff, hisotropic⟩ :=
    exists_native_tip_metric_realization g D hrotation N q s hs.2 htip
  let D0 := D1.withMetric (M35.cylinderEuclideanMetric 0 zero_lt_one)
  obtain ⟨h0, h1, h2⟩ := terminalCurvature_native_two_derivative_bounds he
    (show epsilon ≤ 1 / 2 by linarith) _ hclose g1 D0 q hW hcoeff s hs.2 hpW
  obtain ⟨hang, haxis⟩ := neckModelFrame_ricci D0 q s
  exact neck_reference_ricci_not_isotropic D0 D1 _ neckModelFrame
    (neckModelFrame_isometry s) (cap_model_connection_normal 0 zero_lt_one D0 q s)
    hang haxis he.le hsmall h0 h1 h2 hisotropic

end PoincareMT.Proofs.M47
