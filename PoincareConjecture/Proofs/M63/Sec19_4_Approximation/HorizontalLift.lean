import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProductChartPullback
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductIdentities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {circumference : ℝ} {C : M62.CircleGeometry circumference}

theorem circleProduct_horizontalLift
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (P : M62.CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    {gamma : ℝ → P.Point} {U : Set ℝ} (hU : IsOpen U)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ gamma U)
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s).1}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun s => (⟨(gamma s).1, Y s⟩ : TangentBundle (𝓡 n) M)) U) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent ∞
      (fun s => (⟨gamma s, (P.split (gamma s)).symm (Y s, 0)⟩ :
        TangentBundle (𝓡 (n + 1)) P.Point)) U ∧
    ∀ x ∈ U, P.split (gamma x) (rampHorizontalCovariantDerivative DG gamma
      (fun s => (P.split (gamma s)).symm (Y s, 0)) x) =
        (rampHorizontalCovariantDerivative D (fun s => (gamma s).1) Y x, 0) := by
  let := P.chartedSpace
  let X := fun s => (P.split (gamma s)).symm (Y s, 0)
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hbase : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun s => (gamma s).1) U :=
    hfst.comp_contMDiffOn hgamma
  have hlocal (x : ℝ) (hx : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent ∞
        (fun s => (⟨gamma s, X s⟩ : TangentBundle (𝓡 (n + 1)) P.Point)) x ∧
      P.split (gamma x) (rampHorizontalCovariantDerivative DG gamma X x) =
        (rampHorizontalCovariantDerivative D (fun s => (gamma s).1) Y x, 0) := by
    let p := (gamma x).1
    let e := chartAt (EuclideanSpace ℝ (Fin n)) p
    let V := U ∩ (fun s => (gamma s).1) ⁻¹' e.source
    have hV : IsOpen V := hbase.continuousOn.isOpen_inter_preimage hU e.open_source
    have hxV : x ∈ V := ⟨hx, mem_chart_source _ p⟩
    let v : ℝ → EuclideanSpace ℝ (Fin n) :=
      fun s => mfderiv (𝓡 n) (𝓡 n) e (gamma s).1 (Y s)
    have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
    have ht := he.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      e.open_source.uniqueMDiffOn
    have hcoord := ht.comp (hY.mono (show V ⊆ U from inter_subset_left))
      (fun s (hs : s ∈ V) => hs.2)
    have hv : ContDiffOn ℝ ∞ v V := by
      have h := (contMDiff_snd_tangentBundle_modelSpace
        (EuclideanSpace ℝ (Fin n)) (𝓡 n)).comp_contMDiffOn hcoord
      have h' := h.contDiffOn
      change ContDiffOn ℝ ∞
        (fun s => mfderivWithin (𝓡 n) (𝓡 n) e e.source (gamma s).1 (Y s)) V at h'
      apply h'.congr
      intro s hs
      dsimp only [v]
      rw [mfderivWithin_of_isOpen e.open_source hs.2]
    have hrep (s : ℝ) (hs : s ∈ V) : chartVectorField p (v s) (gamma s).1 = Y s := by
      have hi : (mfderiv (𝓡 n) (𝓡 n) e (gamma s).1).IsInvertible :=
        ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hs.2, rfl⟩
      exact hi.inverse_apply_self (Y s)
    have hXrep (s : ℝ) (hs : s ∈ V) : P.productChartField p (v s) 0 (gamma s) = X s := by
      change (P.split (gamma s)).symm (chartVectorField p (v s) (gamma s).1,
        (0 : ℝ) • C.frame (gamma s).2) = _
      rw [hrep s hs, zero_smul]
    have hgraph : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod (𝓡 (n + 1))) ∞
        (fun s => (s, gamma s)) V :=
      contMDiffOn_id.prodMk (hgamma.mono inter_subset_left)
    have hW := (productChartField_param_smooth P p v 0 hV hv).comp hgraph
      (fun s (hs : s ∈ V) => ⟨hs, hs.2⟩)
    have hX : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent ∞
        (fun s => (⟨gamma s, X s⟩ : TangentBundle (𝓡 (n + 1)) P.Point)) x := by
      apply (hW.contMDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
      filter_upwards [hV.mem_nhds hxV] with s hs
      exact congrArg (fun w => (⟨gamma s, w⟩ : TangentBundle (𝓡 (n + 1)) P.Point))
        (hXrep s hs).symm
    have hformula := circleProduct_pullback_chart_field g D P G DG hG p
      ((hgamma.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      hxV.2 hV hxV v hv 0
    have hprodEq := M62.pullback_congr DG (γ := gamma) (x := x)
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) hXrep)
    have hbaseEq := M62.pullback_congr D (γ := fun s => (gamma s).1) (x := x)
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) hrep)
    rw [hprodEq, hbaseEq] at hformula
    exact ⟨hX, hformula⟩
  exact ⟨fun x hx => (hlocal x hx).1.contMDiffWithinAt, fun x hx => (hlocal x hx).2⟩

theorem circleUnit_pullback_zero {a b : ℝ} {F : RicciFlow n M (Icc a b)}
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma : ℝ → P.charts.Point} {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x) :
    rampHorizontalCovariantDerivative (P.flow.connection t) gamma
      (fun s => P.charts.circleUnit (gamma s)) x = 0 := by
  have hP := M62.circleProduct_identities P
  rw [M62.pullback_ambient_field (P.flow.connection t) hgamma P.charts.circleUnit
    (hP.circle_unit_smooth.mdifferentiableAt (by simp))]
  exact hP.circle_parallel t (gamma x) (curveVelocity gamma x)

end PoincareConjecture.M63
