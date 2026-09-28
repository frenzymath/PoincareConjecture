import PoincareConjecture.Proofs.M49.NeckCoordinates
import PoincareConjecture.Proofs.M49.NullVolume
import PoincareConjecture.Proofs.M49.Mathlib.EuclideanNull

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M49

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}
  {Q : Type v} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
  [T3Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q]

theorem calibratedMetricVolume_image_central_sphere_eq_zero
    (h : RiemannianMetric 3 Q) (N : EpsilonNeck g) {f : M → Q}
    (hf : MDifferentiableOn (𝓡 3) (𝓡 3) f N.central_sphere) :
    calibratedMetricVolume h (f '' N.central_sphere) = 0 := by
  classical
  let c := fun q : UnitTwoSphere => chartAt (EuclideanSpace ℝ (Fin 2)) q
  let e := epsilonNeckEuclideanChart N
  let A := fun q => (e q).source ∩ {x : EuclideanSpace ℝ (Fin 3) | x 2 = 0}
  have hzero : 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have hp := inv_pos.mpr N.epsilon_pos
    exact ⟨neg_neg_of_pos hp, hp⟩
  have hmaps (q : UnitTwoSphere) : MapsTo (e q) (A q) N.central_sphere := by
    intro x hx
    rw [N.central_sphere_eq]
    refine ⟨((c q).symm (cylinderCoordinateEquiv x).1, 0),
      ⟨mem_univ _, mem_singleton 0⟩, ?_⟩
    change N.coordinate_map ((c q).symm (cylinderCoordinateEquiv x).1, 0) =
      N.coordinate_map ((c q).symm (cylinderCoordinateEquiv x).1,
        (cylinderCoordinateEquiv x).2)
    rw [cylinderCoordinateEquiv_apply, hx.2]
  have hnull (q : UnitTwoSphere) : calibratedMetricVolume h ((f ∘ e q) '' A q) = 0 := by
    apply calibratedMetricVolume_image_eq_zero_of_mdifferentiableOn h
    · exact hf.comp
        (((epsilonNeckEuclideanChart_contMDiffOn N q).mdifferentiableOn
          (by simp)).mono inter_subset_left) (hmaps q)
    · exact measure_mono_null inter_subset_right
        (EuclideanSpace.volume_coordinate_hyperplane (2 : Fin 3) 0)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun q : UnitTwoSphere => (c q).source) (fun q => (c q).open_source)
    (by intro q _; exact mem_iUnion.mpr ⟨q, mem_chart_source _ _⟩)
  have hcover : f '' N.central_sphere ⊆ ⋃ q ∈ s, (f ∘ e q) '' A q := by
    rintro _ ⟨y, hy, rfl⟩
    rw [N.central_sphere_eq] at hy
    obtain ⟨⟨z, t⟩, hzt, rfl⟩ := hy
    have ht : t = 0 := hzt.2
    subst t
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp (hs (mem_univ z))
    let x := cylinderCoordinateEquiv.symm ((c q) z, 0)
    have hxL : cylinderCoordinateEquiv x = ((c q) z, 0) :=
      cylinderCoordinateEquiv.apply_symm_apply _
    have hxA : x ∈ A q := by
      constructor
      · rw [epsilonNeckEuclideanChart_source]
        change cylinderCoordinateEquiv x ∈ (c q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
        rw [hxL]
        exact ⟨(c q).map_source hzq, hzero⟩
      · have hx2 := congrArg Prod.snd hxL
        change x 2 = 0
        simpa only [cylinderCoordinateEquiv_apply] using hx2
    refine mem_iUnion₂.mpr ⟨q, hq, x, hxA, ?_⟩
    change f (N.coordinate_map ((c q).symm (cylinderCoordinateEquiv x).1,
      (cylinderCoordinateEquiv x).2)) = f (N.coordinate_map (z, 0))
    rw [hxL, (c q).left_inv hzq]
  exact measure_mono_null hcover
    ((measure_biUnion_null_iff s.countable_toSet).mpr (fun q _ => hnull q))

end PoincareConjecture.M49
