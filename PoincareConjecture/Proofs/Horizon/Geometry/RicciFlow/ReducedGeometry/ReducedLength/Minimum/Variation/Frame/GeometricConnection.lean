import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Coordinate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum
open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem chartConnection_pairing_eq_retainedConnection
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J)
    (v w u : EuclideanSpace ℝ (Fin n)) :
    (F.metric (T - s ^ 2)).inner y
        ((F.connection (T - s ^ 2)).connection (chartFrame x w) y
          (chartFrame x v y)) (chartFrame x u y) =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (chartConnection (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) v w) u := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by
    simpa only [e, extChartAt_source] using hy
  have hz : (s, e y) ∈ chartActionDomain F T x := by
    refine ⟨squareTime_mem_interior_preimage ht, e.map_source hy'⟩
  have hpos : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      0 < chartActionMetric F T x (s, e y) z z := by
    intro z hz'
    exact chartActionMetric_pos F T x hz z hz'
  have hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (chartFrame x v)) y :=
    ((chartFrame_contMDiffOn x v y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (chartFrame x w)) y :=
    ((chartFrame_contMDiffOn x w y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (chartFrame x u)) y :=
    ((chartFrame_contMDiffOn x u y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hK := D.koszul_identity hX hY hZ
  have hbr₁ := chartFrame_mlieBracket hy v w
  have hbr₂ := chartFrame_mlieBracket hy w u
  have hbr₃ := chartFrame_mlieBracket hy u v
  rw [hbr₁, hbr₂, hbr₃] at hK
  have h₁ := chartActionMetric_spatial_apply F T hy ht v w u
  have h₂ := chartActionMetric_spatial_apply F T hy ht w u v
  have h₃ := chartActionMetric_spatial_apply F T hy ht u v w
  have h₁' : fderiv ℝ (chartActionMetric F T x) (s, e y) (0, v) w u =
      mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x w p) (chartFrame x u p)) y
        (chartFrame x v y) := by
    simpa only [spatialFDeriv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, e, g] using h₁
  have h₂' : fderiv ℝ (chartActionMetric F T x) (s, e y) (0, w) u v =
      mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x u p) (chartFrame x v p)) y
        (chartFrame x w y) := by
    simpa only [spatialFDeriv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, e, g] using h₂
  have h₃' : fderiv ℝ (chartActionMetric F T x) (s, e y) (0, u) v w =
      mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
        (chartFrame x u y) := by
    simpa only [spatialFDeriv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, e, g] using h₃
  have hK' : 2 * g.inner y (D.connection (chartFrame x w) y (chartFrame x v y))
      (chartFrame x u y) =
      fderiv ℝ (chartActionMetric F T x) (s, e y) (0, v) w u +
        fderiv ℝ (chartActionMetric F T x) (s, e y) (0, w) u v -
        fderiv ℝ (chartActionMetric F T x) (s, e y) (0, u) v w := by
    have hK0 : 2 * g.inner y (D.connection (chartFrame x w) y (chartFrame x v y))
        (chartFrame x u y) =
        mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x w p) (chartFrame x u p)) y
            (chartFrame x v y) +
          mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x u p) (chartFrame x v p)) y
            (chartFrame x w y) -
          mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
            (chartFrame x u y) := by
      simpa [LeviCivitaData.covariantDerivativeOnFields] using hK
    calc
      _ = mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x w p) (chartFrame x u p)) y
            (chartFrame x v y) +
          mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x u p) (chartFrame x v p)) y
            (chartFrame x w y) -
          mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
            (chartFrame x u y) := hK0
      _ = _ := by rw [← h₁', ← h₂', ← h₃']
  have hc := chartConnection_pairing (chartActionMetric F T x)
    (s, e y) hpos v w u
  have hG : DifferentiableAt ℝ (chartActionMetric F T x) (s, e y) :=
    (((chartActionMetric_contDiffOn F T x) _ hz).contDiffAt
      ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have hsym : ∀ᶠ q in 𝓝 (s, e y), ∀ v w,
      chartActionMetric F T x q v w = chartActionMetric F T x q w v := by
    filter_upwards [(chartActionDomain_open F T x).mem_nhds hz] with q hq
    exact chartActionMetric_symm F T x hq
  have hsw := fderiv_bilinear_symm (chartActionMetric F T x) (s, e y) hG hsym (0, w) u v
  rw [hsw] at hK'
  rw [hc]
  dsimp only [g, D] at hK'
  linarith only [hK']

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
