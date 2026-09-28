import PoincareConjecture.Proofs.M62.Sec19_1_CurvaturePairing
import PoincareConjecture.Proofs.M62.Sec19_1_SpatialConnection
import PoincareConjecture.Proofs.M04.RicciRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

set_option maxHeartbeats 800000 in

theorem codazzi {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point)
    (B C D : TangentSpace (𝓡 n) q.1) :
    G.connection.curvatureTensor q (G.charts.timeVector q)
      (G.charts.horizontal q B) (G.charts.horizontal q C) (G.charts.horizontal q D) =
      (F.connection q.2).covariantTensorDerivative (F.connection q.2).ricciEvaluation
        q.1 ![C, B, D] -
      (F.connection q.2).covariantTensorDerivative (F.connection q.2).ricciEvaluation
        q.1 ![D, B, C] := by
  let := G.charts.chartedSpace
  let S := G.charts
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  let Dt := F.connection q.2
  let K := Dt.covariantTensorDerivative Dt.ricciEvaluation
  let X := fun v : E => PoincareConjecture.Proofs.M09.chartVectorField p v
  let H := fun v : E => S.productChartField p v 0
  let T := S.timeVector
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  have hO : IsOpen {r : S.Point | r.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage S.contMDiff_space.continuous
  have hX (v : E) : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% (X v))
      (chartAt E p).source := PoincareConjecture.Proofs.M09.chartVectorField_smooth p v
  have hH (v : E) : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% (H v))
      {r : S.Point | r.1 ∈ (chartAt E p).source} := S.productChartField_contMDiffOn p v 0
  have hT : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% T) := S.timeVector_smooth
  have hfield (v : E) : S.liftSpatialField (fun _ : ℝ => X v) = H v := by
    funext r
    simp [H, X, SpacetimeCharts.liftSpatialField, SpacetimeCharts.productChartField]
  have hdir (v : E) (r : S.Point) : H v r = S.horizontal r (X v r.1) := by
    simp [H, X, SpacetimeCharts.productChartField]
  have hconn (u v : E) (r : S.Point) (hr : r.1 ∈ (chartAt E p).source) :
      G.charts.split r (G.connection.connection (H v) r (H u r)) =
        ((F.connection r.2).connection (X v) r.1 (X u r.1),
          (F.connection r.2).ricci r.1 (X u r.1) (X v r.1)) := by
    have hreg : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
        (T% (S.liftSpatialField (fun _ : ℝ => X v))) r := by
      rw [hfield]
      exact (hH v).contMDiffAt (hO.mem_nhds hr)
    have h := G.spatial_connection_at (fun _ : ℝ => X v) r hreg (X u r.1)
    rw [hfield] at h
    simpa only [hdir] using h
  have hcross (u v w : E) :
      G.metric.inner q (G.connection.connection (H v) q (H u q))
        (G.connection.connection T q (H w q)) =
        -Dt.ricci p (X w p) (Dt.connection (X v) p (X u p)) := by
    have he := S.horizontal_time_decomposition q
      (G.connection.connection (H v) q (H u q))
    rw [hconn u v q hp] at he
    rw [G.metric.symm, ← he]
    simp only [S, T, map_add, map_smul, G.inner_time, G.time_covariant_vertical,
      smul_eq_mul, mul_zero, add_zero]
    rw [hdir]
    exact G.spatial_time_pairing q (X w p) (Dt.connection (X v) p (X u p))
  have hd (u v w : E) :
      mvfderiv (𝓡 (n + 1))
        (fun r => G.metric.inner r (G.connection.connection (H w) r (H v r)) (T r))
        q (H u q) =
      mvfderiv (𝓡 n) (fun x => Dt.ricci x (X w x) (X v x)) p (X u p) := by
    have hf := (M04.contMDiffOn_connection_pairing G.connection hO
      (hH v) (hH w) hT.contMDiffOn).contMDiffAt (hO.mem_nhds hp)
    have hs := S.mvfderiv_space_slice
      (fun r => G.metric.inner r (G.connection.connection (H w) r (H v r)) (T r)) q
      (hf.mdifferentiableAt (by simp)) (X u p)
    have heq : (fun x : M => G.metric.inner (x, q.2)
        (G.connection.connection (H w) (x, q.2) (H v (x, q.2))) (T (x, q.2))) =ᶠ[𝓝 p]
        (fun x => Dt.ricci x (X w x) (X v x)) := by
      filter_upwards [(chartAt E p).open_source.mem_nhds hp] with x hx
      change G.metric.inner (x, q.2)
        (G.connection.connection (H w) (x, q.2) (H v (x, q.2)))
        (G.charts.timeVector (x, q.2)) = _
      rw [G.inner_time, hconn v w (x, q.2) hx]
      exact M04.ricci_symm Dt x (X v x) (X w x)
    have heq' := congrArg (fun L => L (X u p))
      (heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
    rw [hdir]
    exact hs.trans heq'
  have hRicDiff (u v w : E) :
      mvfderiv (𝓡 n) (fun x => Dt.ricci x (X v x) (X w x)) p (X u p) =
        K p ![X u p, X v p, X w p] +
          Dt.ricci p (Dt.connection (X v) p (X u p)) (X w p) +
          Dt.ricci p (X v p) (Dt.connection (X w) p (X u p)) := by
    have he := M04.covariantTensorDerivativeOnFields_eq Dt
      (M04.isSmoothCovariantTensor_ricciEvaluation Dt) (chartAt E p).open_source
      (X := ![X u, X v, X w])
      (by
        intro i
        fin_cases i
        · exact hX u
        · exact hX v
        · exact hX w) hp
    simp only [M04.covariantTensorDerivativeOnFields, Fin.sum_univ_succ] at he
    change mvfderiv (𝓡 n) (fun x => Dt.ricci x (X v x) (X w x)) p (X u p) -
      (Dt.ricci p (Dt.connection (X v) p (X u p)) (X w p) +
        (Dt.ricci p (X v p) (Dt.connection (X w) p (X u p)) + 0)) =
          K p ![X u p, X v p, X w p] at he
    linarith only [he]
  have hformula (u v w : E) :
      G.connection.curvatureTensor q (H u q) (H v q) (T q) (H w q) =
        K p ![X u p, X w p, X v p] - K p ![X v p, X w p, X u p] := by
    have hh := curvatureTensor_pairing_of_commuting G.connection hO
      (hH u) (hH v) hT.contMDiffOn (hH w) hp
      (S.productChartField_bracket p u v 0 0 q hp)
    rw [hd, hcross, hd, hcross, hRicDiff, hRicDiff] at hh
    have hc := M04.connection_commutator Dt
      (((hX u).contMDiffAt ((chartAt E p).open_source.mem_nhds hp)).mdifferentiableAt (by simp))
      (((hX v).contMDiffAt ((chartAt E p).open_source.mem_nhds hp)).mdifferentiableAt (by simp))
    have hc' : Dt.connection (X v) p (X u p) = Dt.connection (X u) p (X v p) := by
      apply sub_eq_zero.mp
      exact hc.trans
        (PoincareConjecture.Proofs.M09.chartVectorField_bracket p u v p hp)
    rw [M04.ricci_symm Dt p (Dt.connection (X w) p (X u p)) (X v p),
      M04.ricci_symm Dt p (Dt.connection (X w) p (X v p)) (X u p), hc'] at hh
    linarith only [hh]
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hp
  have hvalue (V : TangentSpace (𝓡 n) p) : X (L V) p = V := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self V
  have hpoint (V : TangentSpace (𝓡 n) p) : H (L V) q = S.horizontal q V := by
    rw [hdir, hvalue]
  rw [M04.curvatureTensor_pair_exchange]
  simpa only [hpoint, hvalue] using hformula (L C) (L D) (L B)

end PoincareConjecture.M62.SpacetimeData
