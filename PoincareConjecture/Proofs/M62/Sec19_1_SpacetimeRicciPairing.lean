import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeLocalFrame
import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeScalar
import PoincareConjecture.Proofs.M62.Sec19_1_TimeConnection
import PoincareConjecture.Proofs.M04.CurvatureSymmetries











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem spatial_time_pairing {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point)
    (V W : TangentSpace (𝓡 n) q.1) :
    G.metric.inner q
      (G.connection.connection G.charts.timeVector q (G.charts.horizontal q V))
      (G.charts.horizontal q W) = -(F.connection q.2).ricci q.1 V W := by
  let := G.charts.chartedSpace
  let C := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hvalue (Z : TangentSpace (𝓡 n) p) :
      PoincareConjecture.Proofs.M09.chartVectorField p (L Z) p = Z := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self Z
  let X := PoincareConjecture.Proofs.M09.chartVectorField p (L V)
  let Y := PoincareConjecture.Proofs.M09.chartVectorField p (L W)
  let A := C.productChartField p (L V) 0
  let B := C.productChartField p (L W) 0
  let T := C.timeVector
  have hAq : A q = C.horizontal q V := by
    dsimp only [A, SpacetimeCharts.productChartField]
    rw [zero_smul, add_zero]
    exact congrArg (C.horizontal q) (hvalue V)
  have hBq : B q = C.horizontal q W := by
    dsimp only [B, SpacetimeCharts.productChartField]
    rw [zero_smul, add_zero]
    exact congrArg (C.horizontal q) (hvalue W)
  have hTfield : C.productChartField p 0 1 = T := by
    funext z
    simp [SpacetimeCharts.productChartField, PoincareConjecture.Proofs.M09.chartVectorField,
      VectorField.mpullback, SpacetimeCharts.horizontal, T]
  have hU : IsOpen {z : C.Point | z.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage C.contMDiff_space.continuous
  have hA := (C.productChartField_contMDiffOn p (L V) 0).contMDiffAt (hU.mem_nhds hp)
  have hB := (C.productChartField_contMDiffOn p (L W) 0).contMDiffAt (hU.mem_nhds hp)
  have hT := C.timeVector_smooth q
  have hATbr : VectorField.mlieBracket (𝓡 (n + 1)) A T q = 0 := by
    rw [← hTfield]
    exact C.productChartField_bracket p (L V) 0 0 1 q hp
  have hTBbr : VectorField.mlieBracket (𝓡 (n + 1)) T B q = 0 := by
    rw [← hTfield]
    exact C.productChartField_bracket p 0 (L W) 1 0 q hp
  have hBAbr : VectorField.mlieBracket (𝓡 (n + 1)) B A q = 0 :=
    C.productChartField_bracket p (L W) (L V) 0 0 q hp
  have hAT (z : C.Point) : G.metric.inner z (A z) (T z) = 0 := by
    rw [G.inner_time]
    change (C.split z (C.productChartField p (L V) 0 z)).2 = 0
    rw [C.productChartField_split]
  have hTB (z : C.Point) : G.metric.inner z (T z) (B z) = 0 := by
    rw [G.metric.symm, G.inner_time]
    change (C.split z (C.productChartField p (L W) 0 z)).2 = 0
    rw [C.productChartField_split]
  let f : M × ℝ → ℝ := fun z => (F.metric z.2).inner z.1 (Y z.1) (X z.1)
  have hpair (z : C.Point) : G.metric.inner z (B z) (A z) = f (z.1, (z.2 : ℝ)) := by
    simp [A, B, SpacetimeCharts.productChartField, G.inner_horizontal, f, X, Y, C]
  have hX : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% X) p :=
    (PoincareConjecture.Proofs.M09.chartVectorField_smooth p (L V)).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hp)
  have hY : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% Y) p :=
    (PoincareConjecture.Proofs.M09.chartVectorField_smooth p (L W)).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hp)
  have ht := q.2.property
  have hm := F.smooth.contMDiffAt
    (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (univ_mem : univ ∈ 𝓝 p))
  have hswap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : M × ℝ => (z.2, z.1)) (p, (q.2 : ℝ)) :=
    contMDiffAt_snd.prodMk contMDiffAt_fst
  have hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      f (p, (q.2 : ℝ)) := by
    have hpairAt : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : M × ℝ => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z.1 (f z))
        (p, (q.2 : ℝ)) :=
      (hm.comp (p, (q.2 : ℝ)) hswap).clm_bundle_apply₂
        (hY.comp (p, (q.2 : ℝ)) contMDiffAt_fst)
        (hX.comp (p, (q.2 : ℝ)) contMDiffAt_fst)
    have hscalar := (Bundle.contMDiffAt_totalSpace.mp hpairAt).2
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using hscalar.mdifferentiableAt (by simp)
  have hflow := (F.equation q.2 (Ioo_subset_Icc_self ht) p (Y p) (X p)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hderiv : mvfderiv (𝓡 (n + 1)) (fun z => G.metric.inner z (B z) (A z))
      q (T q) = -2 * (F.connection q.2).ricci q.1 V W := by
    simp_rw [hpair]
    rw [C.mvfderiv_product_time f q hf]
    change deriv (fun t => (F.metric t).inner p (Y p) (X p)) q.2 = _
    rw [hflow.deriv]
    change -2 * (F.connection q.2).ricci p
      (PoincareConjecture.Proofs.M09.chartVectorField p (L W) p)
      (PoincareConjecture.Proofs.M09.chartVectorField p (L V) p) = _
    rw [hvalue, hvalue, M04.ricci_symm (F.connection q.2) p W V]
  have hk := M04.koszul_pairing G.connection (X := A) (Y := T) (Z := B) (x := q)
    (hA.mdifferentiableAt (by simp)) (hT.mdifferentiableAt (by simp))
    (hB.mdifferentiableAt (by simp))
  simp only [hTB, hAT, mvfderiv_const, zero_apply, hATbr, hTBbr, hBAbr,
    map_zero, sub_zero, add_zero, zero_add, hderiv] at hk
  rw [hAq, hBq] at hk
  linarith



theorem spatial_spatial_vertical {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hB : G.charts.IsSmoothField (G.charts.liftSpatialField B))
    (q : G.charts.Point) (V : TangentSpace (𝓡 n) q.1) :
    (G.charts.split q
      (G.connection.connection (G.charts.liftSpatialField B)
        q (G.charts.horizontal q V))).2 =
      (F.connection q.2).ricci q.1 V (B q.2 q.1) := by
  let := G.charts.chartedSpace
  have hzero (r : G.charts.Point) :
      G.metric.inner r (G.charts.liftSpatialField B r) (G.charts.timeVector r) = 0 := by
    rw [G.inner_time]
    simp [SpacetimeCharts.liftSpatialField, SpacetimeCharts.horizontal]
  have h := M04.metric_derivative_pairing G.connection
    (FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1))) (G.charts.horizontal q V))
    ((hB q).mdifferentiableAt (by simp))
    ((G.charts.timeVector_smooth q).mdifferentiableAt (by simp))
  simp only [hzero, mvfderiv_const, zero_apply, FiberBundle.extend_apply_self,
    G.inner_time] at h
  have hneg : G.metric.inner q (G.charts.liftSpatialField B q)
      (G.connection.connection G.charts.timeVector q (G.charts.horizontal q V)) =
        -(F.connection q.2).ricci q.1 V (B q.2 q.1) := by
    rw [G.metric.symm]
    exact G.spatial_time_pairing q V (B q.2 q.1)
  rw [hneg] at h
  linarith

end PoincareConjecture.M62.SpacetimeData
