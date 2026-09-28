import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedRootHeightFirstAmbient










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞


theorem exists_saddle_height_first_transition_ambient
    (U V : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hU : ContDiffOn ℝ ∞ U U.source)
    (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source)
    (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (hUh : ∀ p ∈ U.source, (U p).1 = p.1)
    (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
    (a l r b : ℝ) (hal : a < l) (hlr : l < r) (hrb : r < b)
    (hUs : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ U.source)
    (hVs : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ V.source)
    (hboundary : ∀ z ∈ Icc a b,
      (fun x : E2 => (U (z, x)).2) '' sphere 0 1 =
        (fun x : E2 => (V (z, x)).2) '' sphere 0 1)
    (u : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo l r) :
    ∃ G : D3,
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm
            ((U.symm (V (z, x))).2, z)) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm
            ((V.symm (U (z, x))).2, z)) ∧
      G '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) ∧
      G.symm '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
          (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
  exact exists_saddle_root_height_first_transition_ambient U V hU hUi hV hVi
    hUh hVh a l r b hal hlr hrb hUs hVs hboundary u s hs

end PoincareConjecture.M25.Topology3D
