import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Null images in intrinsic Riemannian volume

Differentiable maps from Euclidean space to a manifold of the same dimension
send Lebesgue-null sets to sets of zero normalized intrinsic Hausdorff volume.
The countable cover is taken in the source, so neither completeness nor a
countable atlas on the carrier is required.

This is the null-image step in the localized cut-locus argument supporting
Morgan--Tian, Theorem 1.34, p. 19. The chart argument is also used in
AxelWorkspace archived revision 231fa639f4eedc671d11203b8f8837e625b38212,
MorganTianLib/Ch01/MeasureNull.lean; here volume is the retained intrinsic
Hausdorff measure and only local differentiability is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The coordinate volume formula sends arbitrary null sets to null sets;
measurability of the null set itself is unnecessary. -/
theorem volumeMeasure_image_eq_zero_of_volume_eq_zero
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : s ⊆ e.source)
    (hnull : volume s = 0) : g.volumeMeasure (e '' s) = 0 := by
  obtain ⟨t, hst, ht, ht0⟩ := exists_measurable_superset_of_null hnull
  apply measure_mono_null (image_mono (subset_inter hst hs))
  rw [g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei
    (ht.inter e.open_source.measurableSet) inter_subset_right]
  exact setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_left ht0)

/-- A differentiable map preserves nullity locally in every target chart. -/
theorem volumeMeasure_image_eq_zero_of_mdifferentiableAt
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {s : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ x ∈ s, MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hnull : volume s = 0) : g.volumeMeasure (f '' s) = 0 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  let : Nonempty s := hne.to_subtype
  have hlocal (x : s) : ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ (x : EuclideanSpace ℝ (Fin n)) ∈ U ∧
      f '' U ⊆ (extChartAt (𝓡 n) (f x)).source := by
    have hN := (hf x x.property).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (f x)).mem_nhds
        (mem_extChartAt_source (I := 𝓡 n) (f x)))
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hN
    exact ⟨U, hUopen, hxU, image_subset_iff.mpr hUsub⟩
  choose U hUopen hxU hU using hlocal
  obtain ⟨a, ha⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    U hUopen (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hcover : f '' s ⊆ ⋃ i : ℕ, f '' (s ∩ U (a i)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ha hx)
    exact mem_iUnion.mpr ⟨i, x, ⟨hx, hi⟩, rfl⟩
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro i
  let c := extChartAt (𝓡 n) (f (a i))
  have hc : f '' (s ∩ U (a i)) ⊆ c.source :=
    (image_mono inter_subset_right).trans (hU (a i))
  have hcoord : volume ((c ∘ f) '' (s ∩ U (a i))) = 0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    · intro x hx
      exact (mdifferentiableAt_iff_differentiableAt.mp
        (((contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := f (a i))).contMDiffAt
          (by simpa only [extChartAt_source] using
            ((isOpen_extChartAt_source (I := 𝓡 n) (f (a i))).mem_nhds
              (hc ⟨x, hx, rfl⟩)))).mdifferentiableAt (by simp) |>.comp x
          (hf x hx.1))).differentiableWithinAt
    · exact measure_mono_null inter_subset_left hnull
  have hsource : (c ∘ f) '' (s ∩ U (a i)) ⊆ c.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hc ⟨x, hx, rfl⟩)
  have hchart := g.volumeMeasure_image_eq_zero_of_volume_eq_zero
    (chartAt (EuclideanSpace ℝ (Fin n)) (f (a i))).symm
    (by simpa [extChartAt_target] using
      (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) (f (a i))))
    (contMDiffOn_extChartAt (I := 𝓡 n) (x := f (a i)))
    (by simpa [c, extChartAt_target] using hsource) hcoord
  convert hchart using 1
  rw [← image_comp]
  congr 1
  apply image_congr
  intro x hx
  exact (c.left_inv (hc ⟨x, hx, rfl⟩)).symm

end PoincareMT.RiemannianMetric
