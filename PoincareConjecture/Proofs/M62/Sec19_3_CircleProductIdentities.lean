import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductRicciDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem circleProduct_identities {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : CircleProductData F circumference) :
    CircleProductIdentities P := by
  let := P.charts.chartedSpace
  let E := EuclideanSpace ℝ (Fin n)
  have hzero (p : M) : PoincareConjecture.Proofs.M09.chartVectorField p (0 : E) = 0 := by
    funext y
    simp only [PoincareConjecture.Proofs.M09.chartVectorField, VectorField.mpullback, map_zero]
    rfl
  have hfield (p : M) : P.charts.productChartField p 0 1 = P.charts.circleUnit := by
    funext q
    simp only [CircleProductCharts.productChartField, hzero, Pi.zero_apply, one_smul,
      CircleProductCharts.circleUnit]
  have hsplit (q : P.charts.Point) :
      P.charts.split q (P.charts.circleUnit q) = (0, P.circle.frame q.2) :=
    (P.charts.split q).apply_symm_apply _
  have hRic (t : ℝ) (q : P.charts.Point) (V W : TangentSpace (𝓡 (n + 1)) q) :=
    circleProduct_ricci (F.metric t) (F.connection t) P.circle P.charts
      (P.flow.metric t) (P.flow.connection t) (P.metric_eq t) q V W
  refine {
    circle_identities := circle_identities P.circle
    circle_unit_smooth := ?_
    circle_unit := ?_
    circle_parallel := ?_
    circle_ricci := ?_
    riemann_split := fun t => circleProduct_curvatureTensor (F.metric t) (F.connection t)
      P.circle P.charts (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)
    ricci_split := hRic
    ricci_derivative_split := fun t => circleProduct_ricci_derivative (F.metric t)
      (F.connection t) P.circle P.charts (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)
  }
  · intro q
    have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
      contMDiff_fst.comp P.charts.to_product_smooth
    have hopen : IsOpen {z : P.charts.Point | z.1 ∈ (chartAt E q.1).source} :=
      (chartAt E q.1).open_source.preimage hfst.continuous
    rw [← hfield q.1]
    exact (P.charts.productChartField_contMDiffOn q.1 0 1).contMDiffAt
      (hopen.mem_nhds (mem_chart_source E q.1))
  · intro t q
    rw [P.metric_eq, hsplit]
    simp only [map_zero, zero_add, (circle_identities P.circle).frame_unit]
  · intro t q V
    have hp : q.1 ∈ (chartAt E q.1).source := mem_chart_source E q.1
    obtain ⟨v, r, hv⟩ := P.charts.productChartField_exists q.1 q hp V
    have h := circleProduct_chart_connection (F.metric t) (F.connection t) P.circle
      P.charts (P.flow.metric t) (P.flow.connection t) (P.metric_eq t) q.1 v 0 r 1 q hp
    rw [hfield, hv, hzero] at h
    simp only [CovariantDerivative.zero, Pi.zero_apply, zero_apply] at h
    apply (P.charts.split q).injective
    rw [map_zero]
    change P.charts.split q ((P.flow.connection t).connection P.charts.circleUnit q V) = (0, 0)
    exact h
  · intro t q V
    rw [hRic, hsplit]
    obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)).1 q.1
    change (F.connection t).ricciEvaluation q.1 ![(P.charts.split q V).1, 0] = 0
    rw [hA]
    exact A.map_coord_zero 1 rfl

end PoincareConjecture.M62
