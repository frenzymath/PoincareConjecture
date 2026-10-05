import PoincareLib.Topology.Manifold.Surgery.Event.Stereographic.StereographicCurvature
import PoincareLib.Geometry.Riemannian.Curvature.Pullback
import PoincareLib.Geometry.RicciFlow.Soliton.Basic

/-!
# Positive unit curvature of the actual sphere metric

At every sphere point the chart with opposite pole is centered at zero.
The Euclidean-source curvature pullback theorem transports the explicit
center calculation to the actual retained sphere connection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M38

/-- The center of an inverse stereographic chart is opposite its pole. -/
theorem threeSphereStereoInverse_zero (a : UnitThreeSphere) :
    threeSphereStereoInverse a 0 = -a := by
  apply Subtype.ext
  rw [threeSphereStereoInverse_coe]
  simp [stereoInvFunAux_apply]

/-- The actual inverse chart has invertible differential at every point. -/
theorem threeSphereStereo_invertible (a : UnitThreeSphere)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse a) z).IsInvertible := by
  change ((threeSphereStereoLocalDiffeomorph a).mfderivToContinuousLinearEquiv
    (by simp) z).toContinuousLinearMap.IsInvertible
  exact ContinuousLinearMap.isInvertible_equiv

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The center curvature formula transfers through any actual local
isometry from this stereographic metric. -/
theorem curvatureTensor_of_stereoIsometry (a : UnitThreeSphere)
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin 3) → M}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f 0)
    (hinv : ∀ᶠ z in 𝓝 0, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible)
    (hmetric : ∀ᶠ z in 𝓝 0, ∀ u v : EuclideanSpace ℝ (Fin 3),
      (threeSphereStereoMetric a).inner z u v =
        g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v))
    (u v w z : EuclideanSpace ℝ (Fin 3)) :
    D.curvatureTensor (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 u)
      (mfderiv (𝓡 3) (𝓡 3) f 0 v) (mfderiv (𝓡 3) (𝓡 3) f 0 w)
      (mfderiv (𝓡 3) (𝓡 3) f 0 z) =
        inner ℝ v z * inner ℝ u w - inner ℝ u z * inner ℝ v w := by
  let DE := (threeSphereStereoMetric a).euclideanLeviCivitaData
  rw [← DE.curvatureTensor_eq_pullback_euclidean D hf hinv hmetric,
    LeviCivitaData.curvatureTensor, threeSphereStereo_curvature_zero,
    threeSphereStereoMetric_inner]
  norm_num [inner_sub_left, real_inner_smul_left]

/-- An orthonormal pair at the image of the chart center has sectional
curvature one. Invertibility supplies its actual coordinate lifts. -/
theorem sectional_one_of_stereoIsometry (a : UnitThreeSphere)
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin 3) → M}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f 0)
    (hinv : ∀ᶠ z in 𝓝 0, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible)
    (hmetric : ∀ᶠ z in 𝓝 0, ∀ u v : EuclideanSpace ℝ (Fin 3),
      (threeSphereStereoMetric a).inner z u v =
        g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v))
    (u v : TangentSpace (𝓡 3) (f 0))
    (hu : g.inner (f 0) u u = 1) (hv : g.inner (f 0) v v = 1)
    (huv : g.inner (f 0) u v = 0) : D.sectionalCurvature (f 0) u v = 1 := by
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  let u₀ := e.symm u
  let v₀ := e.symm v
  have heu : mfderiv (𝓡 3) (𝓡 3) f 0 u₀ = u := by
    rw [← he]
    exact e.apply_symm_apply u
  have hev : mfderiv (𝓡 3) (𝓡 3) f 0 v₀ = v := by
    rw [← he]
    exact e.apply_symm_apply v
  have hm (b c : EuclideanSpace ℝ (Fin 3)) :
      inner ℝ b c = g.inner (f 0)
        (mfderiv (𝓡 3) (𝓡 3) f 0 b) (mfderiv (𝓡 3) (𝓡 3) f 0 c) := by
    have h := hmetric.self_of_nhds b c
    norm_num [threeSphereStereoMetric_inner] at h
    exact h
  have hc := curvatureTensor_of_stereoIsometry a D hf hinv hmetric u₀ v₀ u₀ v₀
  rw [heu, hev, hm, hm, hm, hm, heu, hev, hu, hv, huv, g.symm (f 0) v u, huv]
    at hc
  rw [LeviCivitaData.sectionalCurvature, hc, hu, hv, huv]
  norm_num

/-- The actual induced metric on the unit three-sphere has constant
positive sectional curvature one for every retained Levi-Civita connection. -/
theorem threeSphere_constantPositiveSectionalCurvature
    (D : LeviCivitaData threeSphereMetric) :
    ConstantPositiveSectionalCurvature threeSphereMetric D := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x u v hu hv huv
  have hcenter : threeSphereStereoInverse (-x) 0 = x := by
    rw [threeSphereStereoInverse_zero, neg_neg]
  have hi : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z).IsInvertible :=
    Filter.Eventually.of_forall (threeSphereStereo_invertible (-x))
  have hm : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      ∀ b c : EuclideanSpace ℝ (Fin 3),
        (threeSphereStereoMetric (-x)).inner z b c =
          threeSphereMetric.inner (threeSphereStereoInverse (-x) z)
            (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z b)
            (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z c) :=
    Filter.Eventually.of_forall (fun _ _ _ => rfl)
  have hc := sectional_one_of_stereoIsometry (-x) D
    ((threeSphereStereoLocalDiffeomorph (-x)).contMDiff 0) hi hm
  rw [hcenter] at hc
  exact hc u v hu hv huv

end PoincareMT.M38
