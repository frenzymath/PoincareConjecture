import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coordinates

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem map_restrict_volumeMeasure_coordinate_subset (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : MeasurableSet O) (hOs : O ⊆ e.source) :
    (g.volumeMeasure.restrict (e '' O)).map e.symm =
      (volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict O := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ.restrict O)
    (g.map_restrict_volumeMeasure_symm e he hei)
  have hm : AEMeasurable e.symm (g.volumeMeasure.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  rw [Measure.restrict_map_of_aemeasurable hm hO,
    Measure.restrict_restrict' e.open_target.measurableSet,
    inter_comm (e.symm ⁻¹' O) e.target,
    ← e.image_eq_target_inter_inv_preimage hOs,
    Measure.restrict_restrict_of_subset hOs] at h
  exact h

theorem coordinate_representative_ae (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O) (hOs : O ⊆ e.source)
    {U : EuclideanSpace ℝ (Fin n) → ℝ} {v : M → ℝ}
    (hUv : U =ᵐ[volume.restrict O] fun x => v (e x)) :
    (fun y => U (e.symm y)) =ᵐ[g.volumeMeasure.restrict (e '' O)] v := by
  have hOt : e '' O ⊆ e.target := by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hOs hx)
  have hOimage := e.isOpen_image_of_subset_source hO hOs
  have hac : (g.volumeMeasure.restrict (e '' O)).map e.symm ≪ volume.restrict O := by
    rw [g.map_restrict_volumeMeasure_coordinate_subset e he hei hO.measurableSet hOs]
    exact (withDensity_absolutelyContinuous volume _).restrict O
  have h := ae_of_ae_map
    ((e.symm.continuousOn.mono hOt).aemeasurable hOimage.measurableSet)
    (hac.ae_eq hUv)
  filter_upwards [h, ae_restrict_mem hOimage.measurableSet] with y hy hyO
  simpa only [e.right_inv (hOt hyO)] using hy

theorem exists_smooth_representative_on_coordinate_image (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O) (hOs : O ⊆ e.source)
    (v : Lp ℝ 2 g.volumeMeasure) {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : ContDiffOn ℝ ∞ U O)
    (hUv : U =ᵐ[volume.restrict O] fun x => v (e x)) :
    ∃ F : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F (e '' O) ∧
      F =ᵐ[g.volumeMeasure.restrict (e '' O)] (v : M → ℝ) := by
  have hOt : e '' O ⊆ e.target := by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hOs hx)
  refine ⟨fun y => U (e.symm y), ?_, g.coordinate_representative_ae e he hei hO hOs hUv⟩
  apply hU.contMDiffOn.comp (hei.mono hOt)
  rintro y ⟨x, hx, rfl⟩
  simpa only [mem_preimage, e.left_inv (hOs hx)] using hx

end PoincareConjecture.RiemannianMetric
