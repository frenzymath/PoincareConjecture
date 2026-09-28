import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ProjectedSpeed
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRestriction

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m65ProductChartField_connection (P : M62.CircleProductData F circumference)
    (t : ℝ) (p : M) (w : EuclideanSpace ℝ (Fin n)) (q : P.charts.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (V : TangentSpace (𝓡 (n + 1)) q) :
    P.charts.split q ((P.flow.connection t).connection
      (P.charts.productChartField p w 0) q V) =
      ((F.connection t).connection (Proofs.M09.chartVectorField p w)
        q.1 (P.charts.split q V).1, 0) := by
  obtain ⟨v, r, hv⟩ := P.charts.productChartField_exists p q hq V
  rw [← hv, P.charts.productChartField_split]
  exact M62.circleProduct_chart_connection (F.metric t) (F.connection t)
    P.circle P.charts (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)
    p v w r 0 q hq

theorem m65Projection_field_mdiff (P : M62.CircleProductData F circumference)
    {gamma : ℝ → P.charts.Point}
    {Y : ∀ y, TangentSpace (𝓡 (n + 1)) (gamma y)} {x : ℝ}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun y => (⟨gamma y, Y y⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point)) x) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨(gamma y).1, (P.charts.split (gamma y) (Y y)).1⟩ :
        TangentBundle (𝓡 n) M)) x := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have h := ((hfst.contMDiff_tangentMap (m := ∞) (by simp)).mdifferentiableAt
    (by simp)).comp x hY
  apply h.congr_of_eventuallyEq
  filter_upwards [] with y
  dsimp only [Function.comp_apply, tangentMap]
  rw [TotalSpace.mk_inj, ← P.charts.split_space]

theorem m65Projection_pullback (P : M62.CircleProductData F circumference)
    (t : ℝ) {gamma : ℝ → P.charts.Point}
    {Y : ∀ y, TangentSpace (𝓡 (n + 1)) (gamma y)} {x : ℝ}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun y => (⟨gamma y, Y y⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point)) x) :
    (P.charts.split (gamma x)
      (rampHorizontalCovariantDerivative (P.flow.connection t) gamma Y x)).1 =
      rampHorizontalCovariantDerivative (F.connection t) (fun y => (gamma y).1)
        (fun y => (P.charts.split (gamma y) (Y y)).1) x := by
  let := P.charts.chartedSpace
  let E := EuclideanSpace ℝ (Fin n)
  let p := (gamma x).1
  let Yh := fun y => (P.charts.split (gamma y) (Y y)).1
  let A := (P.charts.split (gamma x)
    (rampHorizontalCovariantDerivative (P.flow.connection t) gamma Y x)).1
  let B := rampHorizontalCovariantDerivative (F.connection t)
    (fun y => (gamma y).1) Yh x
  have hYsplit := hY
  rw [mdifferentiableAt_totalSpace] at hYsplit
  have hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x := hYsplit.1
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hgammah : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => (gamma y).1) x :=
    (hfst.mdifferentiableAt (by simp)).comp x hgamma
  have hYh := m65Projection_field_mdiff P hY
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  have hvelocity := mfderiv_comp_apply (f := gamma)
    (g := (Prod.fst : P.charts.Point → M)) x
    (hfst.mdifferentiableAt (by simp)) hgamma (1 : ℝ)
  change curveVelocity (n := n) (fun y => (gamma y).1) x = _ at hvelocity
  rw [← P.charts.split_space] at hvelocity
  change curveVelocity (n := n) (fun y => (gamma y).1) x =
    (P.charts.split (gamma x) (curveVelocity (n := n + 1) gamma x)).1 at hvelocity
  have hpair (w : E) : (F.metric t).inner p A (Proofs.M09.chartVectorField p w p) =
      (F.metric t).inner p B (Proofs.M09.chartVectorField p w p) := by
    let Z := Proofs.M09.chartVectorField p w
    let Zp := P.charts.productChartField p w 0
    have hZ : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
        (fun q => (⟨q, Z q⟩ : TangentBundle (𝓡 n) M)) p :=
      ((Proofs.M09.chartVectorField_smooth p w).contMDiffAt
        ((chartAt E p).open_source.mem_nhds hp)).mdifferentiableAt (by simp)
    have hopen : IsOpen {q : P.charts.Point | q.1 ∈ (chartAt E p).source} :=
      (chartAt E p).open_source.preimage hfst.continuous
    have hZp : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent
        (fun q => (⟨q, Zp q⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point)) (gamma x) :=
      ((P.charts.productChartField_contMDiffOn p w 0).contMDiffAt
        (hopen.mem_nhds hp)).mdifferentiableAt (by simp)
    have hprod := M62.hasDerivAt_metric_pairing (P.flow.connection t) hgamma hY
      (hZp.comp x hgamma)
    have hbase := M62.hasDerivAt_metric_pairing (F.connection t) hgammah hYh
      (hZ.comp x hgammah)
    have hfun : (fun y => (P.flow.metric t).inner (gamma y) (Y y) (Zp (gamma y))) =
        fun y => (F.metric t).inner (gamma y).1 (Yh y) (Z (gamma y).1) := by
      funext y
      rw [P.metric_eq]
      dsimp only [Zp]
      rw [P.charts.productChartField_split]
      simp only [zero_smul, map_zero, add_zero]
      rfl
    rw [hfun] at hprod
    have heq := hprod.unique hbase
    rw [M62.pullback_ambient_field (P.flow.connection t) hgamma Zp hZp,
      M62.pullback_ambient_field (F.connection t) hgammah Z hZ] at heq
    dsimp only [Zp] at heq
    simp only [P.metric_eq, P.charts.productChartField_split,
      m65ProductChartField_connection P t p w (gamma x) hp,
      zero_smul, map_zero, add_zero] at heq
    rw [hvelocity] at heq
    exact add_right_cancel heq
  change A = B
  by_contra hne
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
  have htest : Proofs.M09.chartVectorField p (L (A - B)) p = A - B :=
    hi.inverse_apply_self (A - B)
  have heq := hpair (L (A - B))
  rw [htest] at heq
  have hzero : (F.metric t).inner p (A - B) (A - B) = 0 := by
    rw [((F.metric t).inner p).map_sub A B]
    change (F.metric t).inner p A (A - B) - (F.metric t).inner p B (A - B) = 0
    exact sub_eq_zero.mpr heq
  exact (F.metric t).pos p (A - B) (sub_ne_zero.mpr hne) |>.ne' hzero

end PoincareConjecture
