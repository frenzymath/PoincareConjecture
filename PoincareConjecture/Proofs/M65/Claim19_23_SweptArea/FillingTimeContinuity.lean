import PoincareConjecture.Proofs.M65.Mathlib.SphereIntervalSection
import PoincareConjecture.Statements.M61Width

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65FillingArea_continuous_time (hM61 : M61RawWidthCore.{u})
    (g : RiemannianMetric 3 M) (compact : IsCompact (Set.univ : Set M))
    {a b : ℝ} (hab : a < b) (c : ContinuousMap (Set.Icc a b) (C1FreeLoopSpace (M := M)))
    (hnull : ∀ t, IsNullHomotopicLoop (c t)) :
    Continuous (fun t => fillingArea g (c t)) := by
  let e := iccHomeoI a b hab
  let family : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
    ⟨fun z => c (e.symm (M65.sphereHeight z)),
      c.continuous.comp (e.symm.continuous.comp M65.sphereHeight.continuous)⟩
  have hfamily : M61NullFamily family := fun z => hnull (e.symm (M65.sphereHeight z))
  have harea := (hM61.family g compact family hfamily).area_continuous
  have h := harea.comp (M65.sphereHeightSection.continuous.comp e.continuous)
  change Continuous (fun t =>
    fillingArea g (c (e.symm (M65.sphereHeight (M65.sphereHeightSection (e t)))))) at h
  simpa only [M65.sphereHeight_section, Homeomorph.symm_apply_apply] using h

end PoincareConjecture
