import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ProductPullbackC1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem auxiliaryCircle_horizontal_pullback_c1
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {gamma : ℝ → P.charts.Point}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma)
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s).1}
    (hY : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n).tangent 1
      (fun s => (⟨(gamma s).1, Y s⟩ : TangentBundle (𝓡 n) M))) (x : ℝ) :
    P.charts.split (gamma x) (rampHorizontalCovariantDerivative (P.flow.connection time)
      gamma (fun s => (P.charts.split (gamma s)).symm (Y s, 0)) x) =
        (rampHorizontalCovariantDerivative (F.connection time)
          (fun s => (gamma s).1) Y x, 0) := by
  let := P.charts.chartedSpace
  let p := (gamma x).1
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let U := (fun s => (gamma s).1) ⁻¹' e.source
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hbase : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun s => (gamma s).1) :=
    (hfst.of_le (by simp)).comp hgamma
  have hU : IsOpen U := e.open_source.preimage hbase.continuous
  have hx : x ∈ U := mem_chart_source _ p
  let v : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) e (gamma s).1 (Y s)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have ht := he.contMDiffOn_tangentMapWithin (m := 1)
    (by norm_num; exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    e.open_source.uniqueMDiffOn
  have hcoord := ht.comp (hY.contMDiffOn (s := U)) (fun s (hs : s ∈ U) => hs)
  have hv : ContDiffOn ℝ 1 v U := by
    have h := (contMDiff_snd_tangentBundle_modelSpace
      (EuclideanSpace ℝ (Fin n)) (𝓡 n)).comp_contMDiffOn hcoord
    have h' := h.contDiffOn
    change ContDiffOn ℝ 1
      (fun s => mfderivWithin (𝓡 n) (𝓡 n) e e.source (gamma s).1 (Y s)) U at h'
    apply h'.congr
    intro s hs
    dsimp only [v]
    rw [mfderivWithin_of_isOpen e.open_source hs]
  have hrep (s : ℝ) (hs : s ∈ U) : chartVectorField p (v s) (gamma s).1 = Y s := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) e (gamma s).1).IsInvertible :=
      ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hs, rfl⟩
    exact hi.inverse_apply_self (Y s)
  have hXrep (s : ℝ) (hs : s ∈ U) :
      P.charts.productChartField p (v s) 0 (gamma s) =
        (P.charts.split (gamma s)).symm (Y s, 0) := by
    change (P.charts.split (gamma s)).symm (chartVectorField p (v s) (gamma s).1,
      (0 : ℝ) • P.circle.frame (gamma s).2) = _
    rw [hrep s hs, zero_smul]
  have hformula := auxiliaryCircle_pullback_chart_field_c1 (F.metric time)
    (F.connection time) P.charts (P.flow.metric time) (P.flow.connection time)
    (P.metric_eq time) p (hgamma.mdifferentiableAt (by simp)) hx hU hx v hv 0
  have hprodEq := M62.pullback_congr (P.flow.connection time) (γ := gamma) (x := x)
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hXrep)
  have hbaseEq := M62.pullback_congr (F.connection time)
    (γ := fun s => (gamma s).1) (x := x)
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hrep)
  rw [hprodEq, hbaseEq] at hformula
  exact hformula

end PoincareConjecture.M64
