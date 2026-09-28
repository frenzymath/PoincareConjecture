import PoincareConjecture.Proofs.M62.Sec19_1_SpatialConnection
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRestriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem covariantAlong_space_slice {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (t : OpenTime a b) {gamma : ℝ → M}
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s)} {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x)
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 n) M)) x) :
    G.charts.split (gamma x, t)
      (G.covariantAlong (fun s => (gamma s, t))
        (fun s => G.charts.horizontal (gamma s, t) (Y s)) x) =
      (rampHorizontalCovariantDerivative (F.connection t) gamma Y x,
        (F.connection t).ricci (gamma x) (curveVelocity gamma x) (Y x)) := by
  let := G.charts.chartedSpace
  let C := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let p := gamma x
  let q : C.Point := (p, t)
  let g := F.metric t
  let D := F.connection t
  let gammahat : ℝ → C.Point := fun s => (gamma s, t)
  let Yhat : (s : ℝ) → TangentSpace (𝓡 (n + 1)) (gammahat s) :=
    fun s => C.horizontal (gammahat s) (Y s)
  let A := rampHorizontalCovariantDerivative G.connection gammahat Yhat x
  let U := (C.split q A).1
  let Z0 := rampHorizontalCovariantDerivative D gamma Y x
  let V := curveVelocity (n := n) gamma x
  have hgammahat : MDifferentiableAt (M' := C.Point) 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gammahat x :=
    ((C.contMDiff_space_slice t).mdifferentiableAt (by simp)).comp x hgamma
  have hvelocity : curveVelocity gammahat x = C.horizontal q V := by
    have h := mfderiv_comp_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (I'' := 𝓡 (n + 1))
      (f := gamma) (g := fun y : M => ((y, t) : C.Point)) x
      ((C.contMDiff_space_slice t).mdifferentiableAt (by simp)) hgamma (1 : ℝ)
    rw [C.mfderiv_space_slice] at h
    exact h
  have hYhat : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun s => (⟨gammahat s, Yhat s⟩ : TangentBundle (𝓡 (n + 1)) C.Point)) x := by
    have h := (((C.contMDiff_space_slice t).contMDiff_tangentMap (m := ∞)
      (by simp)).mdifferentiableAt (by simp)).comp x hY
    apply h.congr_of_eventuallyEq
    filter_upwards [] with s
    simp only [Function.comp_def, tangentMap, C.mfderiv_space_slice, gammahat, Yhat]
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hvalue (W : TangentSpace (𝓡 n) p) :
      PoincareConjecture.Proofs.M09.chartVectorField p (L W) p = W := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self W
  have htest (W : TangentSpace (𝓡 n) p) : g.inner p U W = g.inner p Z0 W := by
    let Z := PoincareConjecture.Proofs.M09.chartVectorField p (L W)
    let B := C.productChartField p (L W) 0
    have hZ : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% Z) p :=
      (PoincareConjecture.Proofs.M09.chartVectorField_smooth p (L W)).contMDiffAt
        ((chartAt E p).open_source.mem_nhds hp)
    have hO : IsOpen {r : C.Point | r.1 ∈ (chartAt E p).source} :=
      (chartAt E p).open_source.preimage C.contMDiff_space.continuous
    have hB : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% B) q :=
      (C.productChartField_contMDiffOn p (L W) 0).contMDiffAt (hO.mem_nhds hp)
    have hZq : Z p = W := hvalue W
    have hBq : B q = C.horizontal q W := by
      change C.horizontal q (Z p) + (0 : ℝ) • C.timeVector q = _
      rw [hZq, zero_smul, add_zero]
    have hfield : C.liftSpatialField (fun _ : ℝ => Z) = B := by
      funext r
      simp [B, Z, SpacetimeCharts.liftSpatialField, SpacetimeCharts.productChartField]
    have hreg : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
        (T% (C.liftSpatialField (fun _ : ℝ => Z))) q := by
      rw [hfield]
      exact hB
    have hconn : G.charts.split q
        (G.connection.connection B q (C.horizontal q V)) =
        (D.connection Z p V, D.ricci p V (Z p)) := by
      have h := G.spatial_connection_at (fun _ : ℝ => Z) q hreg V
      rw [hfield] at h
      exact h
    have hpair : (fun s => G.metric.inner (gammahat s) (Yhat s) (B (gammahat s))) =
        (fun s => g.inner (gamma s) (Y s) (Z (gamma s))) := by
      funext s
      simp only [B, SpacetimeCharts.productChartField, zero_smul, add_zero, Yhat]
      exact G.inner_horizontal (gammahat s) (Y s) (Z (gamma s))
    have hbig := hasDerivAt_metric_pairing G.connection hgammahat hYhat
      ((hB.mdifferentiableAt (by simp)).comp x hgammahat)
    have hsmall := hasDerivAt_metric_pairing D hgamma hY
      ((hZ.mdifferentiableAt (by simp)).comp x hgamma)
    rw [hpair] at hbig
    have he := hbig.unique hsmall
    rw [pullback_ambient_field G.connection hgammahat B (hB.mdifferentiableAt (by simp)),
      pullback_ambient_field D hgamma Z (hZ.mdifferentiableAt (by simp)), hvelocity] at he
    have hsecond : G.metric.inner q (Yhat x)
        (G.connection.connection B q (C.horizontal q V)) =
        g.inner p (Y x) (D.connection Z p V) := by
      rw [G.metric_eq, hconn]
      simp [Yhat, C, SpacetimeCharts.horizontal, gammahat, q, p, g]
    change G.metric.inner q A (B q) +
      G.metric.inner q (Yhat x) (G.connection.connection B q (C.horizontal q V)) =
      g.inner p Z0 (Z p) + g.inner p (Y x) (D.connection Z p V) at he
    rw [hsecond, hBq, hZq, G.metric_eq] at he
    simp only [C, SpacetimeCharts.horizontal, ContinuousLinearEquiv.apply_symm_apply,
      mul_zero, add_zero] at he
    change g.inner p U W + g.inner p (Y x) (D.connection Z p V) =
      g.inner p Z0 W + g.inner p (Y x) (D.connection Z p V) at he
    exact add_right_cancel he
  have hhorizontal : U = Z0 := by
    by_contra hne
    have he := htest (U - Z0)
    have hz : g.inner p (U - Z0) (U - Z0) = 0 := by
      rw [(g.inner p).map_sub U Z0]
      change g.inner p U (U - Z0) - g.inner p Z0 (U - Z0) = 0
      exact sub_eq_zero.mpr he
    exact (ne_of_gt (g.pos p (U - Z0) (sub_ne_zero.mpr hne))) hz
  have hT := (C.timeVector_smooth q).mdifferentiableAt (by simp)
  have hzero (s : ℝ) :
      G.metric.inner (gammahat s) (Yhat s) (C.timeVector (gammahat s)) = 0 := by
    change G.metric.inner (gammahat s) (Yhat s) (G.charts.timeVector (gammahat s)) = 0
    rw [G.inner_time]
    simp [Yhat, C, SpacetimeCharts.horizontal]
  have hbig := hasDerivAt_metric_pairing G.connection hgammahat hYhat
    (hT.comp x hgammahat)
  have hconstant : HasDerivAt
      (fun s => G.metric.inner (gammahat s) (Yhat s) (C.timeVector (gammahat s))) 0 x := by
    simpa only [hzero] using hasDerivAt_const x (0 : ℝ)
  have he := hbig.unique hconstant
  rw [pullback_ambient_field G.connection hgammahat C.timeVector hT, hvelocity] at he
  have hneg : G.metric.inner q (Yhat x)
      (G.connection.connection C.timeVector q (C.horizontal q V)) = -D.ricci p V (Y x) := by
    rw [G.metric.symm]
    exact G.spatial_time_pairing q V (Y x)
  change G.metric.inner q A (G.charts.timeVector q) +
    G.metric.inner q (Yhat x) (G.connection.connection C.timeVector q (C.horizontal q V)) = 0 at he
  rw [G.inner_time, hneg] at he
  apply Prod.ext
  · exact hhorizontal
  · change (C.split q A).2 = D.ricci p V (Y x)
    linarith only [he]

end PoincareConjecture.M62.SpacetimeData
