import PoincareConjecture.Proofs.M08.ChartTensorDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chartModelSection_contMDiffAt {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffAt ℝ ∞ c (extChartAt (𝓡 n) x y)) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p
        (chartFrame x (c (extChartAt (𝓡 n) x p)) p)) y := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  apply (e.contMDiffAt_iff (x₀ := y)
    (f := fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p
      (chartFrame x (c (extChartAt (𝓡 n) x p)) p)) (e.mem_source.mpr hy)).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have h := hc.contMDiffAt.comp y (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hy)
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hy] with p hp
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
  exact e.continuousLinearMapAt_symmL hp _

set_option maxHeartbeats 4000000 in
theorem closedChartChristoffel_spatial_contDiffOn {J C : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContDiffOn ℝ ∞ (fun q ↦ closedChartChristoffel F T x C (s, q) v w)
      (extChartAt (𝓡 n) x).target := by
  let k : EuclideanSpace ℝ (Fin n) →
      (ℝ × EuclideanSpace ℝ (Fin n)) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := fun q ↦ ((s, q), (v, w))
  have hk : ContDiff ℝ ∞ k := (contDiff_const.prodMk contDiff_id).prodMk contDiff_const
  have hm : MapsTo k (extChartAt (𝓡 n) x).target
      ((C ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ univ) :=
    fun q hq ↦ ⟨⟨hs, hq⟩, mem_univ (v, w)⟩
  have h := (closedChartChristoffel_contDiffOn F T x hC htime).comp hk.contDiffOn hm
  exact h

theorem closedChartChristoffel_symm {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v w =
      closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) w v := by
  let D := F.connection (T - s ^ 2)
  have hframe (z : EuclideanSpace ℝ (Fin n)) :=
    ((chartFrame_contMDiffOn x z y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  have h := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero (hframe v) (hframe w)
  rw [chartFrame_mlieBracket hy v w] at h
  have heq := sub_eq_zero.mp h
  rw [closedChartChristoffel_connection F T htime hy hs,
    closedChartChristoffel_connection F T htime hy hs] at heq
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have heq' := congrArg (e.continuousLinearMapAt ℝ y) heq
  change e.continuousLinearMapAt ℝ y
      (e.symmL ℝ y (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v w)) =
    e.continuousLinearMapAt ℝ y
      (e.symmL ℝ y (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) w v)) at heq'
  simpa only [e.continuousLinearMapAt_symmL hy] using heq'

set_option maxHeartbeats 1500000 in
theorem curvature_chart {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (u v z : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).curvature y
        (chartFrame x u y) (chartFrame x v y) (chartFrame x z y) =
      chartFrame x
        (fderiv ℝ (fun q ↦ closedChartChristoffel F T x C (s, q) v z)
            (extChartAt (𝓡 n) x y) u -
          fderiv ℝ (fun q ↦ closedChartChristoffel F T x C (s, q) u z)
            (extChartAt (𝓡 n) x y) v +
          closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) u
            (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v z) -
          closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v
            (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) u z)) y := by
  let D := F.connection (T - s ^ 2)
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have ht := e.map_source hy'
  let Γ := fun q ↦ closedChartChristoffel F T x C (s, q)
  have hΓ (a b : EuclideanSpace ℝ (Fin n)) : ContDiffAt ℝ ∞ (fun q ↦ Γ q a b) (e y) :=
    ((closedChartChristoffel_spatial_contDiffOn F T x hC htime hs a b) _ ht).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht)
  have heq (a b : EuclideanSpace ℝ (Fin n)) :
      ∀ᶠ p in 𝓝 y, D.connection (chartFrame x b) p (chartFrame x a p) =
        chartFrame x (Γ (e p) a b) p := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy] with p hp
    exact closedChartChristoffel_connection F T htime hp hs a b
  have hX (a b : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p
          (D.connection (chartFrame x b) p (chartFrame x a p))) y := by
    apply (chartModelSection_contMDiffAt hy (fun q ↦ Γ q a b) (hΓ a b)).congr_of_eventuallyEq
    filter_upwards [heq a b] with p hp
    exact congrArg (fun v : TangentSpace (𝓡 n) p ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p v) hp
  have hconn (a b c : EuclideanSpace ℝ (Fin n)) :=
    connection_chart_section F T htime hy hs
      (fun p ↦ D.connection (chartFrame x c) p (chartFrame x b p)) (hX b c)
      (fun q ↦ Γ q b c) ((hΓ b c).differentiableAt (by simp)) (heq b c) a
  have hcurv := (hM04.tensor_calculus n M (F.metric (T - s ^ 2)) D).2.2.2.2
    (chartAt (EuclideanSpace ℝ (Fin n)) x).source
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
    (chartFrame x u) (chartFrame x v) (chartFrame x z)
    (chartFrame_contMDiffOn x u) (chartFrame_contMDiffOn x v) (chartFrame_contMDiffOn x z) y hy
  rw [← hcurv]
  unfold LeviCivitaData.curvatureOnFields
  rw [chartFrame_mlieBracket hy u v, map_zero, sub_zero, hconn u v z, hconn v u z]
  simp only [chartFrame, map_add, map_sub]
  abel

theorem curvatureTensor_chart {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (u v w z : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).curvatureTensor y
        (chartFrame x u y) (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (fderiv ℝ (fun q ↦ closedChartChristoffel F T x C (s, q) v z)
            (extChartAt (𝓡 n) x y) u -
          fderiv ℝ (fun q ↦ closedChartChristoffel F T x C (s, q) u z)
            (extChartAt (𝓡 n) x y) v +
          closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) u
            (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v z) -
          closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v
            (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) u z)) w := by
  unfold LeviCivitaData.curvatureTensor
  rw [curvature_chart F hM04 T hC htime hy hs u v z, chartActionMetric_apply F T hy s]

end PoincareConjecture.M08
