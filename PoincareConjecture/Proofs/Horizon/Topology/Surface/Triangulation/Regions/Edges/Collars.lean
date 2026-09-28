


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Trimming








set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))


noncomputable def edgeCurve (a : D.EdgeIndex) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  coordinateCircleArc
    (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M) a.1.1) (D.radius a.1.1)
    ((a.1.2 : ℝ) * Real.pi)
    (D.cut a.1 a.2.castSucc + t * (D.cut a.1 a.2.succ - D.cut a.1 a.2.castSucc))

omit [T2Space M] in
theorem edge_map_eq (a : D.EdgeIndex) (t : ℝ) :
    (D.edge a.1 a.2).map t =
      (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).symm (D.edgeCurve a t) :=
  D.edge_map a.1 a.2 t

omit [T2Space M] in
theorem cut_mem_Icc (i : D.centers × Fin 2) (k : Fin (D.edgeCount i + 1)) :
    D.cut i k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa only [(D.cut_strictMono i).2.1] using (D.cut_strictMono i).1.monotone (Fin.zero_le k)
  · simpa only [(D.cut_strictMono i).2.2] using (D.cut_strictMono i).1.monotone (Fin.le_last k)

omit [T2Space M] in
theorem edgeCurve_smooth (a : D.EdgeIndex) : ContDiff ℝ ∞ (D.edgeCurve a) :=
  coordinateCircleArc_affine_contDiff _ _ _ _ _

omit [T2Space M] in
theorem edgeCurve_injective (a : D.EdgeIndex) : InjOn (D.edgeCurve a) (Icc (0 : ℝ) 1) :=
  coordinateCircleArc_affine_injOn _ (D.radius_pos a.1.1 a.1.1.property) _
    (D.cut_mem_Icc a.1 a.2.castSucc).1 ((D.cut_strictMono a.1).1 Fin.castSucc_lt_succ)
    (D.cut_mem_Icc a.1 a.2.succ).2

omit [T2Space M] in
theorem edgeCurve_regular (a : D.EdgeIndex) (t : ℝ) : deriv (D.edgeCurve a) t ≠ 0 :=
  coordinateCircleArc_affine_deriv_ne_zero _ (D.radius_pos a.1.1 a.1.1.property) _
    ((D.cut_strictMono a.1).1 Fin.castSucc_lt_succ) t

omit [T2Space M] in
theorem edgeCurve_target (a : D.EdgeIndex) : D.edgeCurve a '' Icc (0 : ℝ) 1 ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).target := by
  rintro z ⟨t, _, rfl⟩
  exact D.closedBall_subset_target a.1.1 a.1.1.property (sphere_subset_closedBall
    (coordinateCircleArc_mem_sphere _ (D.radius_pos a.1.1 a.1.1.property).le _ _))

omit [T2Space M] in
theorem chartArcCarrier_edgeCurve (a : D.EdgeIndex) (l r : ℝ) :
    chartArcCarrier (a.1.1 : M) (D.edgeCurve a) l r = (D.edge a.1 a.2).map '' Icc l r := by
  simp only [chartArcCarrier, image_image]
  congr 1
  funext t
  exact (D.edge_map_eq a t).symm



theorem exists_trimmed_collars (U V : D.EdgeIndex → Set M)
    (hU : ∀ a, U a ∈ 𝓝 ((D.edge a.1 a.2).map 0))
    (hV : ∀ a, V a ∈ 𝓝 ((D.edge a.1 a.2).map 1)) :
    ∃ (l r ε : D.EdgeIndex → ℝ)
      (C : D.EdgeIndex → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M),
      (∀ a, 0 < l a ∧ l a < r a ∧ r a < 1 ∧ 0 < ε a) ∧
      (∀ a, (D.edge a.1 a.2).map '' Icc 0 (l a) ⊆ U a ∧
        (D.edge a.1 a.2).map '' Icc (r a) 1 ⊆ V a) ∧
      (∀ a, collarParameterEquiv ⁻¹' (Icc (l a) (r a) ×ˢ Ioo (-ε a) (ε a)) ⊆
        (C a).source) ∧
      (∀ a t, C a (collarParameterEquiv.symm (t, 0)) = (D.edge a.1 a.2).map t) ∧
      (∀ a, (C a).target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).source) ∧
      (∀ a, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C a) (C a).source) ∧
      (∀ a, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C a).symm (C a).target) ∧
      Pairwise (fun a b => Disjoint (C a).target (C b).target) ∧
      (∀ a b, a ≠ b → Disjoint (C a).target ((D.edge b.1 b.2).map '' Icc (0 : ℝ) 1)) := by
  have hmeet (a b : D.EdgeIndex) (hab : a ≠ b) :
      chartArcCarrier (a.1.1 : M) (D.edgeCurve a) 0 1 ∩
        chartArcCarrier (b.1.1 : M) (D.edgeCurve b) 0 1 ⊆
      {(chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).symm (D.edgeCurve a 0),
        (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).symm (D.edgeCurve a 1)} := by
    rw [D.chartArcCarrier_edgeCurve, D.chartArcCarrier_edgeCurve,
      ← D.edge_map_eq a 0, ← D.edge_map_eq a 1]
    exact fun z hz => (D.edge_intersection a b hab hz).1
  obtain ⟨l, r, ε, C, hbounds, hends, hstrip, hformula, hchart, hC, hCinv, hdis, havoid⟩ :=
    exists_trimmed_disjoint_chart_arc_collars (fun a : D.EdgeIndex => (a.1.1 : M))
      D.edgeCurve D.edgeCurve_smooth D.edgeCurve_injective (fun a t _ => D.edgeCurve_regular a t)
      D.edgeCurve_target hmeet U V
      (fun a => by rw [← D.edge_map_eq]; exact hU a)
      (fun a => by rw [← D.edge_map_eq]; exact hV a)
  refine ⟨l, r, ε, C, hbounds, ?_, hstrip, ?_, hchart, hC, hCinv, hdis, ?_⟩
  · intro a
    simpa only [D.chartArcCarrier_edgeCurve] using hends a
  · intro a t
    rw [hformula, collarParameterEquiv.apply_symm_apply,
      Poincare.Topology.Plane.Curves.normalStrip_axis, ← D.edge_map_eq]
  · intro a b hab
    simpa only [D.chartArcCarrier_edgeCurve] using havoid a b hab

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
