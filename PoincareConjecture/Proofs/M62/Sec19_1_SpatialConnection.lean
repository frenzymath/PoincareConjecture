import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeSlices
import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeRicciPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem spatial_chart_connection_pairing {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (p : M)
    (v w z : EuclideanSpace ℝ (Fin n)) (q : G.charts.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    G.metric.inner q
      (G.connection.connection (G.charts.productChartField p w 0) q
        (G.charts.productChartField p v 0 q))
      (G.charts.productChartField p z 0 q) =
    (F.metric q.2).inner q.1
      ((F.connection q.2).connection
        (PoincareConjecture.Proofs.M09.chartVectorField p w) q.1
        (PoincareConjecture.Proofs.M09.chartVectorField p v q.1))
      (PoincareConjecture.Proofs.M09.chartVectorField p z q.1) := by
  let := G.charts.chartedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : G.charts.Point → Type _) :=
    ⟨G.metric.toRiemannianMetric⟩
  let C := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let X := fun u : E => PoincareConjecture.Proofs.M09.chartVectorField p u
  let A := fun u : E => C.productChartField p u 0
  have hU : IsOpen {r : C.Point | r.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage C.contMDiff_space.continuous
  have hA (u : E) : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% (A u)) q :=
    (C.productChartField_contMDiffOn p u 0).contMDiffAt (hU.mem_nhds hq)
  have hX (u : E) : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% (X u)) q.1 :=
    (PoincareConjecture.Proofs.M09.chartVectorField_smooth p u).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hq)
  have hd (u v w : E) :
      mvfderiv (𝓡 (n + 1)) (fun r => G.metric.inner r (A v r) (A w r)) q (A u q) =
        mvfderiv (𝓡 n) (fun x => (F.metric q.2).inner x (X v x) (X w x)) q.1
          (X u q.1) := by
    have h := C.mvfderiv_space_slice (fun r => G.metric.inner r (A v r) (A w r)) q
      (((hA v).inner_bundle (hA w)).mdifferentiableAt (by simp)) (X u q.1)
    simpa only [A, X, C, SpacetimeCharts.productChartField, zero_smul, add_zero,
      G.inner_horizontal] using h
  have hb (u v : E) : VectorField.mlieBracket (𝓡 (n + 1)) (A u) (A v) q = 0 :=
    C.productChartField_bracket p u v 0 0 q hq
  have hbx (u v : E) : VectorField.mlieBracket (𝓡 n) (X u) (X v) q.1 = 0 :=
    PoincareConjecture.Proofs.M09.chartVectorField_bracket p u v q.1 hq
  have h := M04.koszul_pairing G.connection (X := A v) (Y := A w) (Z := A z)
    ((hA v).mdifferentiableAt (by simp)) ((hA w).mdifferentiableAt (by simp))
    ((hA z).mdifferentiableAt (by simp))
  have hs := M04.koszul_pairing (F.connection q.2) (X := X v) (Y := X w) (Z := X z)
    ((hX v).mdifferentiableAt (by simp)) ((hX w).mdifferentiableAt (by simp))
    ((hX z).mdifferentiableAt (by simp))
  simp only [hb, map_zero, zero_apply, sub_zero, add_zero, hd] at h
  simp only [hbx, map_zero, zero_apply, sub_zero, add_zero] at hs
  linarith only [h, hs]

theorem spatial_spatial_horizontal {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (q : G.charts.Point)
    (hB : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% (G.charts.liftSpatialField B)) q)
    (V : TangentSpace (𝓡 n) q.1) :
    (G.charts.split q
      (G.connection.connection (G.charts.liftSpatialField B) q
        (G.charts.horizontal q V))).1 =
      (F.connection q.2).connection (B q.2) q.1 V := by
  let := G.charts.chartedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : G.charts.Point → Type _) :=
    ⟨G.metric.toRiemannianMetric⟩
  let C := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  let D := F.connection q.2
  let g := F.metric q.2
  let U := (C.split q (G.connection.connection (C.liftSpatialField B) q (C.horizontal q V))).1
  let Z := D.connection (B q.2) p V
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hvalue (W : TangentSpace (𝓡 n) p) :
      PoincareConjecture.Proofs.M09.chartVectorField p (L W) p = W := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self W
  have hproduct (W : TangentSpace (𝓡 n) p) :
      C.productChartField p (L W) 0 q = C.horizontal q W := by
    dsimp only [SpacetimeCharts.productChartField]
    rw [zero_smul, add_zero]
    exact congrArg (C.horizontal q) (hvalue W)
  have hBs := C.liftSpatialField_slice_smoothAt B q hB
  have htest (W : TangentSpace (𝓡 n) p) : g.inner p U W = g.inner p Z W := by
    let Y := PoincareConjecture.Proofs.M09.chartVectorField p (L W)
    let A := C.productChartField p (L W) 0
    have hYs : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% Y) p :=
      (PoincareConjecture.Proofs.M09.chartVectorField_smooth p (L W)).contMDiffAt
        ((chartAt E p).open_source.mem_nhds hp)
    have hopen : IsOpen {r : C.Point | r.1 ∈ (chartAt E p).source} :=
      (chartAt E p).open_source.preimage C.contMDiff_space.continuous
    have hA : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% A) q :=
      (C.productChartField_contMDiffOn p (L W) 0).contMDiffAt (hopen.mem_nhds hp)
    have hAq : A q = C.horizontal q W := hproduct W
    have hYq : Y p = W := hvalue W
    have hd := C.mvfderiv_space_slice
      (fun r => G.metric.inner r (C.liftSpatialField B r) (A r)) q
      ((hB.inner_bundle hA).mdifferentiableAt (by simp)) V
    have hslice (x : M) :
        G.metric.inner (x, q.2) (C.liftSpatialField B (x, q.2)) (A (x, q.2)) =
          g.inner x (B q.2 x) (Y x) := by
      simp only [A, SpacetimeCharts.productChartField, zero_smul, add_zero,
        SpacetimeCharts.liftSpatialField]
      exact G.inner_horizontal (x, q.2) (B q.2 x) (Y x)
    simp_rw [hslice] at hd
    have h := M04.metric_derivative_pairing G.connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1))) (C.horizontal q V))
      (hB.mdifferentiableAt (by simp)) (hA.mdifferentiableAt (by simp))
    have hs := M04.metric_derivative_pairing D (FiberBundle.extend E V)
      (hBs.mdifferentiableAt (by simp)) (hYs.mdifferentiableAt (by simp))
    simp only [FiberBundle.extend_apply_self] at h hs
    have hfixed := G.spatial_chart_connection_pairing p (L V) (L W) (L (B q.2 p)) q hp
    change G.metric.inner q
      (G.connection.connection A q (C.productChartField p (L V) 0 q))
      (C.productChartField p (L (B q.2 p)) 0 q) =
        g.inner p (D.connection Y p (PoincareConjecture.Proofs.M09.chartVectorField p (L V) p))
          (PoincareConjecture.Proofs.M09.chartVectorField p (L (B q.2 p)) p) at hfixed
    rw [hproduct, hproduct, hvalue, hvalue] at hfixed
    have hsecond : G.metric.inner q (C.liftSpatialField B q)
        (G.connection.connection A q (C.horizontal q V)) =
          g.inner p (B q.2 p) (D.connection Y p V) := by
      rw [G.metric.symm, g.symm]
      exact hfixed
    change mvfderiv (𝓡 (n + 1))
        (fun r => G.metric.inner r (C.liftSpatialField B r) (A r)) q (C.horizontal q V) =
      G.metric.inner q (G.connection.connection (C.liftSpatialField B) q (C.horizontal q V))
        (A q) + G.metric.inner q (C.liftSpatialField B q)
        (G.connection.connection A q (C.horizontal q V)) at h
    rw [hd, hsecond, hAq, G.metric_eq] at h
    simp only [C, SpacetimeCharts.horizontal, ContinuousLinearEquiv.apply_symm_apply,
      mul_zero, add_zero] at h
    change mvfderiv (𝓡 n) (fun x => g.inner x (B q.2 x) (Y x)) p V =
      g.inner p U W + g.inner p (B q.2 p) (D.connection Y p V) at h
    change mvfderiv (𝓡 n) (fun x => g.inner x (B q.2 x) (Y x)) p V =
      g.inner p Z (Y p) + g.inner p (B q.2 p) (D.connection Y p V) at hs
    rw [hYq] at hs
    linarith only [h, hs]
  by_contra hne
  have hpair := htest (U - Z)
  have hz : g.inner p (U - Z) (U - Z) = 0 := by
    rw [(g.inner p).map_sub U Z]
    change g.inner p U (U - Z) - g.inner p Z (U - Z) = 0
    exact sub_eq_zero.mpr hpair
  exact (ne_of_gt (g.pos p (U - Z) (sub_ne_zero.mpr hne))) hz

theorem spatial_connection_at {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (q : G.charts.Point)
    (hB : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% (G.charts.liftSpatialField B)) q)
    (V : TangentSpace (𝓡 n) q.1) :
    G.charts.split q
      (G.connection.connection (G.charts.liftSpatialField B) q
        (G.charts.horizontal q V)) =
      ((F.connection q.2).connection (B q.2) q.1 V,
        (F.connection q.2).ricci q.1 V (B q.2 q.1)) := by
  let := G.charts.chartedSpace
  apply Prod.ext
  · exact G.spatial_spatial_horizontal B q hB V
  · have hzero (r : G.charts.Point) :
        G.metric.inner r (G.charts.liftSpatialField B r) (G.charts.timeVector r) = 0 := by
      rw [G.inner_time]
      simp [SpacetimeCharts.liftSpatialField, SpacetimeCharts.horizontal]
    have h := M04.metric_derivative_pairing G.connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1))) (G.charts.horizontal q V))
      (hB.mdifferentiableAt (by simp))
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

theorem spatial_connection {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hB : G.charts.IsSmoothField (G.charts.liftSpatialField B))
    (q : G.charts.Point) (V : TangentSpace (𝓡 n) q.1) :
    G.charts.split q
      (G.connection.connection (G.charts.liftSpatialField B) q
        (G.charts.horizontal q V)) =
      ((F.connection q.2).connection (B q.2) q.1 V,
        (F.connection q.2).ricci q.1 V (B q.2 q.1)) :=
  G.spatial_connection_at B q (hB q) V

end PoincareConjecture.M62.SpacetimeData
