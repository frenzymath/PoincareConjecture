import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteDoubleRelation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts
import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates
import PoincareConjecture.Proofs.M76.Wall.CutDiskProjection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation












set_option autoImplicit false

open Set Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}



theorem Step.projected_source_mate_unique (step : Step s t)
    {Z : Type*} {A : Set Z} {j : Z → t.Carrier} (hj : InjOn j A)
    {x y z : Z} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hpy : step.projection (step.inclusion (j x)) = step.projection (step.inclusion (j y)))
    (hpz : step.projection (step.inclusion (j x)) = step.projection (step.inclusion (j z))) :
    y = z := by
  have hne : j x ≠ j y := fun h ↦ hxy (hj hx hy h)
  have hsub : ({j x, j y} : Set t.Carrier) ⊆
      (step.projection ∘ step.inclusion) ⁻¹' {step.projection (step.inclusion (j x))} := by
    intro a ha
    rcases mem_insert_iff.mp ha with rfl | ha
    · rfl
    · rw [mem_singleton_iff] at ha
      subst a
      exact hpy.symm
  have hpair := eq_of_subset_of_ncard_le hsub
    (by rw [ncard_pair hne]; exact (step.projectionInclusion_fiber _).2)
    (step.projectionInclusion_fiber _).1
  have hzpair : j z ∈ ({j x, j y} : Set t.Carrier) := hpair.symm.subset hpz.symm
  rcases mem_insert_iff.mp hzpair with hzx | hzy
  · exact False.elim (hxz (hj hx hz hzx.symm))
  · exact hj hy hz (mem_singleton_iff.mp hzy).symm



theorem Step.exists_finite_source_double_locus (step : Step s t)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space ↦ j x)) :
    let p := (step.projection ∘ step.inclusion) ∘ j
    PolyhedralPLInCharts s.charts p K.space ∧
      IsLocallyInjective (fun x : K.space ↦ p x) ∧
      ∃ (L : SimplicialComplex ℝ (V × V)) (D : SimplicialComplex ℝ V),
        L.faces.Finite ∧ D.faces.Finite ∧
        L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
          p z.1 = p z.2 ∧ z.1 ≠ z.2} ∧
        D.space = Prod.fst '' L.space ∧ D.space = doubleLocusOn p K.space ∧
        IsCompact D.space ∧ D.space ⊆ K.space := by
  dsimp only
  let p := (step.projection ∘ step.inclusion) ∘ j
  have hp : PolyhedralPLInCharts s.charts p K.space :=
    hj.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ ↦ congrFun (step.chart_forward k) x)
  have hlocal : IsLocallyInjective (fun x : K.space ↦ p x) :=
    step.projectionInclusion_local.isLocallyInjective.comp_right hji.continuous hji.injective
  obtain ⟨L, hL, hLs⟩ := hp.exists_finite_double_relation_complex s.compatible K hK hlocal
  obtain ⟨D, hD, hDs, _⟩ := (L.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ V V).toContinuousAffineMap).exists_finite_triangulation_image hL
  have hdouble : D.space = doubleLocusOn p K.space := by
    rw [hDs, hLs]
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab, hne⟩, rfl⟩
      exact ⟨ha, b, hb, hab, hne⟩
    · rintro ⟨hx, y, hy, hxy, hne⟩
      exact ⟨(x, y), ⟨hx, hy, hxy, hne⟩, rfl⟩
  refine ⟨hp, hlocal, L, D, hL, hD, hLs, hDs, hdouble,
    D.isCompact_space_of_finite hD, ?_⟩
  intro x hx
  exact (hdouble.subset hx).1

end Geometry.OriginalPLTower
