import PoincareLib.Geometry.Riemannian.Soul.Point.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connected distance spheres in radial coordinates

The distance-preserving radial homeomorphism identifies each positive distance
sphere with the image of the unit two-sphere. This proves the connectedness
and compactness used in the separating-neck argument, without assuming either
property as a field of the point-soul data.

Reference: Morgan--Tian, Lemma 2.20 and Proposition 2.19, pp. 31--32.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RiemannianMetric.RadialHomeomorph

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]
  {g : RiemannianMetric 3 M} {p : M}

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

/-- The whole distance sphere is the image of the radial slice, including
surjectivity onto all ambient points of that radius. -/
theorem distanceSphere_eq_range (H : RadialHomeomorph g p) {r : ℝ} (hr : 0 < r) :
    distanceSphere g p r =
      Set.range (fun q : UnitTwoSphere =>
        (H.toHomeomorph (q, ⟨r, hr⟩) : M)) := by
  ext x
  constructor
  · intro hx
    have hxp : x ≠ p := by
      intro heq
      subst x
      have hzero : (g.edist p p).toReal = 0 := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
            (TangentSpace (𝓡 3) : M → Type _) :=
          ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
        let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
        have he : g.edist p p = 0 := Manifold.riemannianEDist_self
        rw [he, ENNReal.toReal_zero]
      exact hr.ne (hzero.symm.trans hx)
    let z := H.toHomeomorph.symm ⟨x, hxp⟩
    have hz : (H.toHomeomorph z : M) = x :=
      congrArg Subtype.val (H.toHomeomorph.apply_symm_apply ⟨x, hxp⟩)
    have hrz : (z.2 : ℝ) = r := by
      rw [← H.distance_eq z, hz]
      exact hx
    refine ⟨z.1, ?_⟩
    have hpair : (z.1, (⟨r, hr⟩ : {r : ℝ // r ∈ Ioi 0})) = z := by
      apply Prod.ext
      · rfl
      · exact Subtype.ext hrz.symm
    change (H.toHomeomorph (z.1, ⟨r, hr⟩) : M) = x
    rw [hpair, hz]
  · rintro ⟨q, rfl⟩
    exact H.distance_eq (q, ⟨r, hr⟩)

/-- Every positive distance sphere in radial coordinates is connected. -/
theorem isConnected_distanceSphere (H : RadialHomeomorph g p) {r : ℝ} (hr : 0 < r) :
    IsConnected (distanceSphere g p r) := by
  rw [H.distanceSphere_eq_range hr]
  exact isConnected_range
    (continuous_subtype_val.comp (H.toHomeomorph.continuous.comp
      (continuous_id.prodMk continuous_const)))

/-- Every positive distance sphere in radial coordinates is compact. -/
theorem isCompact_distanceSphere (H : RadialHomeomorph g p) {r : ℝ} (hr : 0 < r) :
    IsCompact (distanceSphere g p r) := by
  rw [H.distanceSphere_eq_range hr]
  exact isCompact_range
    (continuous_subtype_val.comp (H.toHomeomorph.continuous.comp
      (continuous_id.prodMk continuous_const)))

end PoincareMT.RiemannianMetric.RadialHomeomorph
