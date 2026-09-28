import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeRicciPairing
import PoincareConjecture.Proofs.M62.Sec19_1_MetricVariation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

namespace SpacetimeCharts



theorem mfderiv_time_slice (C : SpacetimeCharts n M a b)
    (p : M) (t : OpenTime a b) (r : ℝ) :
    mfderiv (M' := C.Point) 𝓘(ℝ, ℝ) (𝓡 (n + 1))
      (fun s : OpenTime a b => (p, s)) t r =
        r • C.timeVector (p, t) := by
  let := C.chartedSpace
  have h := mfderiv_comp_apply
    (I := 𝓘(ℝ, ℝ)) (I' := (𝓡 n).prod 𝓘(ℝ, ℝ)) (I'' := 𝓡 (n + 1))
    (f := fun s : OpenTime a b => ((p, s) : SpacetimeCarrier M a b))
    (g := (id : SpacetimeCarrier M a b → C.Point)) t
    (C.from_product_smooth.mdifferentiableAt (by simp))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) r
  erw [mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id] at h
  apply (C.split (p, t)).injective
  change C.split (p, t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (id ∘ fun s : OpenTime a b => ((p, s) :
      SpacetimeCarrier M a b)) t r) = _
  rw [h]
  erw [C.split_mfderiv_from_product]
  simp [timeVector, mfderiv_id, mfderiv_const]
  rfl



theorem mvfderiv_time_slice (C : SpacetimeCharts n M a b)
    (f : C.Point → ℝ) (g : ℝ → ℝ) (q : C.Point) (d : ℝ)
    (hf : MDifferentiableAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f q)
    (hg : HasDerivAt g d (q.2 : ℝ))
    (heq : ∀ s : OpenTime a b, f (q.1, s) = g s) :
    mvfderiv (𝓡 (n + 1)) f q (C.timeVector q) = d := by
  let := C.chartedSpace
  have hj : ContMDiff (M' := C.Point) 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞
      (fun s : OpenTime a b => (q.1, s)) :=
    C.from_product_smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have h := mfderiv_comp_apply (f := fun s : OpenTime a b => ((q.1, s) : C.Point))
    (g := f) q.2 hf (hj.mdifferentiableAt (by simp)) (1 : ℝ)
  rw [C.mfderiv_time_slice, one_smul] at h
  have hg' := mfderiv_comp_apply (f := (Subtype.val : OpenTime a b → ℝ))
    (g := g) q.2 hg.differentiableAt.mdifferentiableAt
    (contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)) (1 : ℝ)
  rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val] at hg'
  have hval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (q.2 : ℝ) (1 : ℝ) = d := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ g (q.2 : ℝ) (1 : ℝ) = d
    rw [hg.hasFDerivAt.fderiv]
    simp
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : OpenTime a b => g s) q.2 (1 : ℝ) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (q.2 : ℝ) (1 : ℝ) at hg'
  rw [hval] at hg'
  have hfun : (fun s : OpenTime a b => f (q.1, s)) = (fun s : OpenTime a b => g s) :=
    funext heq
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : OpenTime a b => f (q.1, s)) q.2 (1 : ℝ) =
    mvfderiv (𝓡 (n + 1)) f q (C.timeVector q) at h
  rw [hfun] at h
  exact h.symm.trans hg'



theorem liftSpatialField_time_smooth (C : SpacetimeCharts n M a b)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hB : C.IsSmoothField (C.liftSpatialField B))
    (p : M) (t : OpenTime a b) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun r : ℝ => (⟨p, B r p⟩ : TangentBundle (𝓡 n) M)) (t : ℝ) := by
  have h := ((C.liftSpatialField_smooth_iff B).mp hB).comp
    ((contMDiff_const (c := p)).prodMk contMDiff_id)
  exact contMDiffAt_subtype_iff.mp (h t)

end SpacetimeCharts

namespace SpacetimeData



theorem time_spatial_pairing {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hB : G.charts.IsSmoothField (G.charts.liftSpatialField B))
    (q : G.charts.Point) (W : TangentSpace (𝓡 n) q.1) :
    G.metric.inner q
      (G.connection.connection (G.charts.liftSpatialField B) q
        (G.charts.timeVector q)) (G.charts.horizontal q W) =
      (F.metric q.2).inner q.1 (fixedPointTimeDerivative B q.1 q.2) W -
        (F.connection q.2).ricci q.1 (B q.2 q.1) W := by
  let := G.charts.chartedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : G.charts.Point → Type _) :=
    ⟨G.metric.toRiemannianMetric⟩
  let C := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  let T := C.timeVector
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hvalue : PoincareConjecture.Proofs.M09.chartVectorField p (L W) p = W := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self W
  let A := C.productChartField p (L W) 0
  have hAr (s : OpenTime a b) : A (p, s) = C.horizontal (p, s) W := by
    dsimp only [A, SpacetimeCharts.productChartField]
    rw [zero_smul, add_zero, hvalue]
  have hAq : A q = C.horizontal q W := hAr q.2
  have hopen : IsOpen {r : C.Point | r.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage C.contMDiff_space.continuous
  have hA : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% A) q :=
    (C.productChartField_contMDiffOn p (L W) 0).contMDiffAt (hopen.mem_nhds hp)
  have hTfield : C.productChartField p 0 1 = T := by
    funext r
    simp [SpacetimeCharts.productChartField, PoincareConjecture.Proofs.M09.chartVectorField,
      VectorField.mpullback, SpacetimeCharts.horizontal, T]
  have hbr : VectorField.mlieBracket (𝓡 (n + 1)) T A q = 0 := by
    rw [← hTfield]
    exact C.productChartField_bracket p 0 (L W) 1 0 q hp
  have hcomm := M04.connection_commutator G.connection (X := T) (Y := A)
    ((C.timeVector_smooth q).mdifferentiableAt (by simp)) (hA.mdifferentiableAt (by simp))
  rw [hbr] at hcomm
  have hconn := sub_eq_zero.mp hcomm
  have hsecond : G.metric.inner q (C.liftSpatialField B q)
      (G.connection.connection A q (T q)) = -(F.connection q.2).ricci p (B q.2 p) W := by
    rw [G.metric.symm, hconn, hAq]
    change G.metric.inner q
      (G.connection.connection C.timeVector q (C.horizontal q W))
      (C.horizontal q (B q.2 p)) = _
    rw [G.spatial_time_pairing, M04.ricci_symm (F.connection q.2) p W (B q.2 p)]
  have hBt := C.liftSpatialField_time_smooth B hB p q.2
  have hflow := hasDerivAt_flow_metric_pairing F (γ := fun _ : ℝ => p)
    (Y := fun r => B r p) (Z := fun _ => W) q.2.property
    mdifferentiableAt_const (hBt.mdifferentiableAt (by simp)) mdifferentiableAt_const
  have hpull : rampHorizontalCovariantDerivative (F.connection q.2)
      (fun _ : ℝ => p) (fun r => B r p) q.2 = fixedPointTimeDerivative B p q.2 := by
    simp only [rampHorizontalCovariantDerivative, fixedPointTimeDerivative,
      curveVelocity, mfderiv_const, zero_apply, map_zero, add_zero]
  have hconst : rampHorizontalCovariantDerivative (F.connection q.2)
      (fun _ : ℝ => p) (fun _ => W) q.2 = 0 := by
    simp only [rampHorizontalCovariantDerivative, curveVelocity, mfderiv_const,
      zero_apply, deriv_const, map_zero, zero_add]
  rw [hpull, hconst] at hflow
  simp only [map_zero, add_zero] at hflow
  have heq (s : OpenTime a b) :
      G.metric.inner (p, s) (C.liftSpatialField B (p, s)) (A (p, s)) =
        (F.metric s).inner p (B s p) W := by
    rw [hAr]
    exact G.inner_horizontal (p, s) (B s p) W
  have hd := C.mvfderiv_time_slice
    (fun r => G.metric.inner r (C.liftSpatialField B r) (A r))
    (fun r => (F.metric r).inner p (B r p) W) q _
    (((hB q).inner_bundle hA).mdifferentiableAt (by simp)) hflow heq
  have h := M04.metric_derivative_pairing G.connection T
    ((hB q).mdifferentiableAt (by simp)) (hA.mdifferentiableAt (by simp))
  change mvfderiv (𝓡 (n + 1))
      (fun r => G.metric.inner r (C.liftSpatialField B r) (A r)) q (T q) =
    G.metric.inner q (G.connection.connection (C.liftSpatialField B) q (T q)) (A q) +
      G.metric.inner q (C.liftSpatialField B q) (G.connection.connection A q (T q)) at h
  rw [hd, hAq, hsecond] at h
  linarith only [h]

end SpacetimeData

end PoincareConjecture.M62
