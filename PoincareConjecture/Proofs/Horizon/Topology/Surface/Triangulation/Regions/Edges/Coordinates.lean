import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Collars

set_option autoImplicit false
open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in
theorem edgeCurve_mem_target (a : D.EdgeIndex) (t : ℝ) :
    D.edgeCurve a t ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).target :=
  D.closedBall_subset_target a.1.1 a.1.1.property (sphere_subset_closedBall
    (coordinateCircleArc_mem_sphere _ (D.radius_pos a.1.1 a.1.1.property).le _ _))

omit [T2Space M] in
theorem edge_contMDiff (a : D.EdgeIndex) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (D.edge a.1 a.2).map := by
  have heq : (D.edge a.1 a.2).map =
      (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).symm ∘ D.edgeCurve a :=
    funext (D.edge_map_eq a)
  rw [heq]
  exact (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := (a.1.1 : M))).comp_contMDiff
    (D.edgeCurve_smooth a).contMDiff (D.edgeCurve_mem_target a)

omit [T2Space M] in
theorem edge_mfderiv_injective (a : D.EdgeIndex) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge a.1 a.2).map t) := by
  have heq : (D.edge a.1 a.2).map =
      (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).symm ∘ D.edgeCurve a :=
    funext (D.edge_map_eq a)
  rw [heq, mfderiv_comp t
    ((mdifferentiable_chart (I := 𝓡 2) (a.1.1 : M)).mdifferentiableAt_symm
      (D.edgeCurve_mem_target a t))
    ((D.edgeCurve_smooth a).differentiable (by simp) t).mdifferentiableAt,
    mfderiv_eq_fderiv]
  apply ((mdifferentiable_chart (I := 𝓡 2) (a.1.1 : M)).symm.mfderiv_injective
    (D.edgeCurve_mem_target a t)).comp
  change Function.Injective (fderiv ℝ (D.edgeCurve a) t)
  intro u v huv
  rw [fderiv_eq_smul_deriv, fderiv_eq_smul_deriv] at huv
  exact smul_left_injective ℝ (D.edgeCurve_regular a t) huv

omit [T2Space M] in
theorem edge_coordinate_contDiffOn (a : D.EdgeIndex)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) :
    ContDiffOn ℝ ∞ (C.symm ∘ (D.edge a.1 a.2).map)
      ((D.edge a.1 a.2).map ⁻¹' C.target) :=
  (hCinv.comp (D.edge_contMDiff a).contMDiffOn (fun _ ht => ht)).contDiffOn

omit [T2Space M] in
theorem edge_coordinate_deriv_ne_zero (a : D.EdgeIndex)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    {t : ℝ} (ht : (D.edge a.1 a.2).map t ∈ C.target) :
    deriv (C.symm ∘ (D.edge a.1 a.2).map) t ≠ 0 := by
  have hdiff : C.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hC.mdifferentiableOn (by simp), hCinv.mdifferentiableOn (by simp)⟩
  have hinj : Function.Injective (fderiv ℝ (C.symm ∘ (D.edge a.1 a.2).map) t) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp t (hdiff.symm.mdifferentiableAt ht)
      ((D.edge_contMDiff a).mdifferentiable (by simp) t)]
    exact (hdiff.symm.mfderiv_injective ht).comp (D.edge_mfderiv_injective a t)
  intro hzero
  have heq : (fderiv ℝ (C.symm ∘ (D.edge a.1 a.2).map) t) 1 =
      (fderiv ℝ (C.symm ∘ (D.edge a.1 a.2).map) t) 0 := by
    simp only [fderiv_apply_one_eq_deriv, hzero, map_zero]
  exact one_ne_zero (hinj heq)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
