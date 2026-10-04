import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectiveMetric
import PoincareLib.Topology.Manifold.Surgery.Event.Three.ThreeSphereCurvature

/-!
# Positive curvature on the actual projective model

Compose its actual antipodal cover with an inverse stereographic chart.
The composite is locally diffeomorphic and preserves the literal coordinate
metric. The already computed center curvature therefore gives sectional
curvature one on the supplied projective carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M38

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]

/-- The actual projective-cover composite has smooth local inverse sheets. -/
theorem projectiveStereo_localDiffeomorph (C : StandardProjectiveSmoothCover Q)
    (a : UnitThreeSphere) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.cover ∘ threeSphereStereoInverse a) :=
  fun z => (threeSphereStereoLocalDiffeomorph a z).comp
    (𝓡 3) Q (C.local_diffeomorph (threeSphereStereoInverse a z))

/-- The composite chart pulls the descended projective metric back to the
same explicit stereographic metric. -/
theorem projectiveStereo_metric (C : StandardProjectiveSmoothCover Q)
    (a : UnitThreeSphere) (z u v : EuclideanSpace ℝ (Fin 3)) :
    (threeSphereStereoMetric a).inner z u v =
      (projectiveMetric C).inner ((C.cover ∘ threeSphereStereoInverse a) z)
        (mfderiv (𝓡 3) (𝓡 3) (C.cover ∘ threeSphereStereoInverse a) z u)
        (mfderiv (𝓡 3) (𝓡 3) (C.cover ∘ threeSphereStereoInverse a) z v) := by
  let e := threeSphereStereoInverse a
  have hc : mfderiv (𝓡 3) (𝓡 3) (C.cover ∘ e) z =
      (mfderiv (𝓡 3) (𝓡 3) C.cover (e z)).comp (mfderiv (𝓡 3) (𝓡 3) e z) :=
    mfderiv_comp z
      ((C.local_diffeomorph.contMDiff (e z)).mdifferentiableAt (by simp))
      ((threeSphereStereoLocalDiffeomorph a).contMDiff z |>.mdifferentiableAt (by simp))
  change threeSphereMetric.inner (e z)
    (mfderiv (𝓡 3) (𝓡 3) e z u) (mfderiv (𝓡 3) (𝓡 3) e z v) = _
  rw [projectiveMetric_inner C]
  change _ = (projectiveMetric C).inner (C.cover (e z))
    (mfderiv (𝓡 3) (𝓡 3) (C.cover ∘ e) z u)
    (mfderiv (𝓡 3) (𝓡 3) (C.cover ∘ e) z v)
  rw [hc]
  rfl

/-- The descended metric has constant positive sectional curvature one
on the literal projective model, for every retained compatible connection. -/
theorem projective_constantPositiveSectionalCurvature
    (C : StandardProjectiveSmoothCover Q) (D : LeviCivitaData (projectiveMetric C)) :
    ConstantPositiveSectionalCurvature (projectiveMetric C) D := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro y u v hu hv huv
  obtain ⟨x, rfl⟩ := C.surjective y
  let f := C.cover ∘ threeSphereStereoInverse (-x)
  have hf := projectiveStereo_localDiffeomorph C (-x)
  have hcenter : f 0 = C.cover x := by
    simp only [f, Function.comp_apply, threeSphereStereoInverse_zero, neg_neg]
  have hi : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible := by
    apply Filter.Eventually.of_forall
    intro z
    change (hf.mfderivToContinuousLinearEquiv (by simp) z).toContinuousLinearMap.IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
  have hm : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      ∀ b c : EuclideanSpace ℝ (Fin 3),
        (threeSphereStereoMetric (-x)).inner z b c =
          (projectiveMetric C).inner (f z)
            (mfderiv (𝓡 3) (𝓡 3) f z b) (mfderiv (𝓡 3) (𝓡 3) f z c) :=
    Filter.Eventually.of_forall (projectiveStereo_metric C (-x))
  have hc := sectional_one_of_stereoIsometry (-x) D (f := f) (hf.contMDiff 0) hi hm
  rw [hcenter] at hc
  exact hc u v hu hv huv

end PoincareMT.M38
