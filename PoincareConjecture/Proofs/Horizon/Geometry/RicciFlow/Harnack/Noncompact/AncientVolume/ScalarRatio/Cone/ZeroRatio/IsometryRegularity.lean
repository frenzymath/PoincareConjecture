import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.IsometricCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.NormalEndpoints
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.IsometryLipschitz
import Mathlib.Analysis.Calculus.Rademacher

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.RiemannianMetric

theorem contDiffOn_of_lipschitzOn_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {C : ℝ≥0} (hLip : LipschitzOnWith C f U)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y) :
    ContDiffOn ℝ ∞ f U := by
  intro p hp
  suffices ContDiffAt ℝ ∞ f p from this.contDiffWithinAt
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  obtain ⟨W, Γ, G, hW, _, _, hΓ, hGW, hGt, hGmap, hGinv⟩ :=
    g.exists_joint_normal_endpoints_in_open hU hp
  have hΓ' : ∀ z ∈ W, g.IsGeodesicOn (Γ z) (Ioo (-2 : ℝ) 2) ∧
      Γ z 0 = z.1 ∧ HasDerivAt (Γ z) z.2 0 ∧ MapsTo (Γ z) (Ioo (-2 : ℝ) 2) U := by
    simpa using hΓ
  have hGt' : (p, p) ∈ G.target := by simpa using hGt
  have hGmap' : ∀ z ∈ G.source, G z = (z.1, Γ z 1) := by simpa using hGmap
  have hnear : {q : E | (q, p) ∈ G.target} ∈ 𝓝 p :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (G.open_target.mem_nhds hGt')
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hp) hnear)
  have hLip' : LipschitzOnWith C f (Metric.ball p r) :=
    hLip.mono (fun q hq => (hsub hq).1)
  obtain ⟨q, hqball, hqdiff⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt (Metric.isOpen_ball.measure_pos (volume : Measure E) ⟨p, Metric.mem_ball_self hr⟩))
    ((ae_restrict_iff' measurableSet_ball).mpr
      (hLip'.ae_differentiableWithinAt_of_mem (μ := volume)))
  have hqf : DifferentiableAt ℝ f q := hqdiff.differentiableAt
    (Metric.isOpen_ball.mem_nhds hqball)
  have hqt : (q, p) ∈ G.target := (hsub hqball).2
  have hfirst (y : E) (hy : (q, y) ∈ G.target) : (G.symm (q, y)).1 = q := by
    exact congrArg Prod.fst ((hGmap' _ (G.map_target hy)).symm.trans (G.right_inv hy))
  have hend (y : E) (hy : (q, y) ∈ G.target) : Γ (q, (G.symm (q, y)).2) 1 = y := by
    have hh := congrArg Prod.snd ((hGmap' _ (G.map_target hy)).symm.trans (G.right_inv hy))
    have hz : G.symm (q, y) = (q, (G.symm (q, y)).2) := Prod.ext (hfirst y hy) rfl
    change Γ (G.symm (q, y)) 1 = y at hh
    rw [hz] at hh
    exact hh
  let v₀ : E := (G.symm (q, p)).2
  have hv₀ : (q, v₀) ∈ W := by
    have hh := hGW (G.map_target hqt)
    have hz : G.symm (q, p) = (q, v₀) := Prod.ext (hfirst p hqt) rfl
    rwa [hz] at hh
  have hvnear : ∀ᶠ v : E in 𝓝 v₀, (q, v) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds hv₀)
  let H : E → ℝ → F := fun v t => f (Γ (q, v) t)
  have hgeo : ∀ᶠ v : E in 𝓝 v₀, h.IsGeodesicOn (H v) (Ioo (-2 : ℝ) 2) := by
    filter_upwards [hvnear] with v hv
    exact ((hΓ' _ hv).1.comp_of_edist_eq h hdist isOpen_Ioo (hΓ' _ hv).2.2.2).1
  have hzero : (fun v => H v 0) =ᶠ[𝓝 v₀] fun _ => f q := by
    filter_upwards [hvnear] with v hv
    simp only [H, (hΓ' _ hv).2.1]
  have hvel : (fun v => deriv (H v) 0) =ᶠ[𝓝 v₀] fun v => fderiv ℝ f q v := by
    filter_upwards [hvnear] with v hv
    have hdf : HasFDerivAt f (fderiv ℝ f q) (Γ (q, v) 0) := by
      rw [(hΓ' _ hv).2.1]
      exact hqf.hasFDerivAt
    exact (hdf.comp_hasDerivAt 0 (hΓ' _ hv).2.2.1).deriv
  have hHs : ContMDiffAt (𝓡 n) (𝓡 m) ∞ (fun v => H v 1) v₀ := by
    apply contMDiffAt_geodesic_endpoint hgeo (convex_Ioo _ _)
      (by norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2) (by norm_num : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2)
    · exact contMDiffAt_const.congr_of_eventuallyEq hzero
    · simpa using (fderiv ℝ f q).contDiff.contDiffAt.congr_of_eventuallyEq hvel
  let Z : E → E := fun y => (G.symm (q, y)).2
  have hZ : ContDiffAt ℝ ∞ Z p :=
    ((hGinv.contDiffAt (G.open_target.mem_nhds hqt)).comp p
      (contDiffAt_const.prodMk contDiffAt_id)).snd
  have hcomposed : ContDiffAt ℝ ∞ ((fun v => H v 1) ∘ Z) p := by
    apply ContDiffAt.comp (f := Z) (g := fun v => H v 1) p
    · exact contMDiffAt_iff_contDiffAt.mp hHs
    · exact hZ
  have heq : f =ᶠ[𝓝 p] fun y => H (Z y) 1 := by
    have htarget : ∀ᶠ y : E in 𝓝 p, (q, y) ∈ G.target :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (G.open_target.mem_nhds hqt)
    filter_upwards [htarget] with y hy
    exact congrArg f (hend y hy).symm
  exact hcomposed.congr_of_eventuallyEq heq

theorem contDiffOn_of_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y) :
    ContDiffOn ℝ ∞ f U := by
  intro p hp
  obtain ⟨V, hV, hpV, hVU, C, hLip⟩ := g.exists_lipschitzOn_of_edist_eq h hU hdist hp
  exact ((g.contDiffOn_of_lipschitzOn_edist_eq h hV hLip
    (fun x hx y hy => hdist x (hVU hx) y (hVU hy))).contDiffAt
      (hV.mem_nhds hpV)).contDiffWithinAt

end PoincareConjecture.RiemannianMetric
