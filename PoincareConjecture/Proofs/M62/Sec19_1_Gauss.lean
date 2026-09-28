import PoincareConjecture.Proofs.M62.Sec19_1_CurvaturePairing
import PoincareConjecture.Proofs.M62.Sec19_1_SpatialConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem gauss {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point)
    (A B C D : TangentSpace (𝓡 n) q.1) :
    G.connection.curvatureTensor q
      (G.charts.horizontal q A) (G.charts.horizontal q B)
      (G.charts.horizontal q C) (G.charts.horizontal q D) =
      (F.connection q.2).curvatureTensor q.1 A B C D -
        (F.connection q.2).ricci q.1 B D * (F.connection q.2).ricci q.1 A C +
        (F.connection q.2).ricci q.1 A D * (F.connection q.2).ricci q.1 B C := by
  let := G.charts.chartedSpace
  let S := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  let g := F.metric q.2
  let Dt := F.connection q.2
  let X := fun v : E => PoincareConjecture.Proofs.M09.chartVectorField p v
  let H := fun v : E => S.productChartField p v 0
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  have hO : IsOpen {r : S.Point | r.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage S.contMDiff_space.continuous
  have hX (v : E) : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% (X v))
      (chartAt E p).source := PoincareConjecture.Proofs.M09.chartVectorField_smooth p v
  have hH (v : E) : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% (H v))
      {r : S.Point | r.1 ∈ (chartAt E p).source} := S.productChartField_contMDiffOn p v 0
  have hfield (v : E) : S.liftSpatialField (fun _ : ℝ => X v) = H v := by
    funext r
    simp [H, X, SpacetimeCharts.liftSpatialField, SpacetimeCharts.productChartField]
  have hconn (u v : E) :
      G.charts.split q (G.connection.connection (H v) q (H u q)) =
        (Dt.connection (X v) p (X u p), Dt.ricci p (X u p) (X v p)) := by
    have hreg : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
        (T% (S.liftSpatialField (fun _ : ℝ => X v))) q := by
      rw [hfield]
      exact (hH v).contMDiffAt (hO.mem_nhds hp)
    have h := G.spatial_connection_at (fun _ : ℝ => X v) q hreg (X u p)
    rw [hfield] at h
    simpa only [H, SpacetimeCharts.productChartField, zero_smul, add_zero] using h
  have hcross (u v w z : E) :
      G.metric.inner q (G.connection.connection (H v) q (H u q))
        (G.connection.connection (H z) q (H w q)) =
      g.inner p (Dt.connection (X v) p (X u p)) (Dt.connection (X z) p (X w p)) +
        Dt.ricci p (X u p) (X v p) * Dt.ricci p (X w p) (X z p) := by
    rw [G.metric_eq, hconn, hconn]
  have hd (u v w z : E) :
      mvfderiv (𝓡 (n + 1))
        (fun r => G.metric.inner r (G.connection.connection (H w) r (H v r)) (H z r))
        q (H u q) =
      mvfderiv (𝓡 n) (fun x => g.inner x (Dt.connection (X w) x (X v x)) (X z x))
        p (X u p) := by
    have hf := (M04.contMDiffOn_connection_pairing G.connection hO (hH v) (hH w) (hH z)).contMDiffAt
      (hO.mem_nhds hp)
    have hs := S.mvfderiv_space_slice
      (fun r => G.metric.inner r (G.connection.connection (H w) r (H v r)) (H z r)) q
      (hf.mdifferentiableAt (by simp)) (X u p)
    have heq : (fun x : M => G.metric.inner (x, q.2)
        (G.connection.connection (H w) (x, q.2) (H v (x, q.2))) (H z (x, q.2))) =ᶠ[𝓝 p]
        (fun x => g.inner x (Dt.connection (X w) x (X v x)) (X z x)) := by
      filter_upwards [(chartAt E p).open_source.mem_nhds hp] with x hx
      exact G.spatial_chart_connection_pairing p v w z (x, q.2) hx
    have heq' := congrArg (fun L => L (X u p))
      (heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
    have hdir : H u q = S.horizontal q (X u p) := by
      simp [H, X, SpacetimeCharts.productChartField, p]
    rw [hdir]
    exact hs.trans heq'
  have hformula (u v w z : E) :
      G.connection.curvatureTensor q (H u q) (H v q) (H w q) (H z q) =
        Dt.curvatureTensor p (X u p) (X v p) (X w p) (X z p) -
          Dt.ricci p (X v p) (X z p) * Dt.ricci p (X u p) (X w p) +
          Dt.ricci p (X u p) (X z p) * Dt.ricci p (X v p) (X w p) := by
    have hh := curvatureTensor_pairing_of_commuting G.connection hO
      (hH u) (hH v) (hH w) (hH z) hp
      (S.productChartField_bracket p u v 0 0 q hp)
    have hs := curvatureTensor_pairing_of_commuting Dt (chartAt E p).open_source
      (hX u) (hX v) (hX w) (hX z) hp
      (PoincareConjecture.Proofs.M09.chartVectorField_bracket p u v p hp)
    rw [hd, hcross, hd, hcross] at hh
    linarith only [hh, hs]
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hvalue (V : TangentSpace (𝓡 n) p) : X (L V) p = V := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self V
  have hpoint (V : TangentSpace (𝓡 n) p) : H (L V) q = S.horizontal q V := by
    change S.horizontal q (X (L V) p) + (0 : ℝ) • S.timeVector q = _
    rw [hvalue, zero_smul, add_zero]
  simpa only [hpoint, hvalue] using hformula (L A) (L B) (L C) (L D)

end PoincareConjecture.M62.SpacetimeData
