import PoincareConjecture.Proofs.M47.CanonicalNeckModelFrame
import PoincareConjecture.Proofs.M47.CanonicalNeckTipRealization
import PoincareConjecture.Proofs.M47.CanonicalNeckTipIsotropy
import PoincareConjecture.Proofs.M47.TerminalCurvatureNativeBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.ChangeMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

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

end PoincareConjecture.Proofs.M47
