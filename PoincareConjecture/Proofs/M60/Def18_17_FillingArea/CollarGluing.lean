import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PiecewiseArea
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRegularity
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Pointwise Bundle NNReal ENNReal

attribute [local instance] Classical.propDecidable

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] [T2Space M]

theorem m60DiskGluing_of_collar (g : RiemannianMetric 3 M)
    {γ γ' : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (H : LoopPlane → M)
    (σ : CircleReparameterization)
    (hmatch : ∀ z : LoopPlane, ‖z‖ = r → D.map (r⁻¹ • z) = H z)
    (hboundary : ∀ z : LoopCircle, H z = γ' (σ.map z))
    {L : ℝ} (hL : 0 ≤ L)
    (hLipH : ∀ x ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
        g.edist (H x) (H y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖)
    (hareaH : IntegrableOn (m60AreaDensity g H)
      ((closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet) volume) :
    ∃ D' : LipschitzSpanningDisk g γ',
      D'.map = (closedBall (0 : LoopPlane) r).piecewise
        (fun z => D.map (r⁻¹ • z)) H ∧
      D'.area = D.area +
        ∫ z in (closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet, m60AreaDensity g H z := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let F : LoopPlane → M := (closedBall (0 : LoopPlane) r).piecewise
    (fun z => D.map (r⁻¹ • z)) H
  have hin (z : LoopPlane) (hz : z ∈ closedBall (0 : LoopPlane) r) :
      r⁻¹ • z ∈ loopDiskSet := by
    rw [← m60_inv_smul_closedBall hr]
    exact smul_mem_smul_set hz
  let K : ℝ≥0 := NNReal.mk (D.lipschitz_constant * r⁻¹)
    (mul_nonneg D.lipschitz_nonnegative (inv_nonneg.mpr hr.le))
  let C : ℝ≥0 := max K (NNReal.mk L hL)
  have hLipInner : LipschitzOnWith K (fun z => D.map (r⁻¹ • z))
      (loopDiskSet ∩ {z : LoopPlane | ‖z‖ ≤ r}) := by
    intro x hx y hy
    have hx' : x ∈ closedBall (0 : LoopPlane) r := by
      simpa only [mem_closedBall, dist_zero_right, mem_ofPred_eq] using hx.2
    have hy' : y ∈ closedBall (0 : LoopPlane) r := by
      simpa only [mem_closedBall, dist_zero_right, mem_ofPred_eq] using hy.2
    have hb := D.lipschitz_on_disk ⟨r⁻¹ • x, hin x hx'⟩ ⟨r⁻¹ • y, hin y hy'⟩
    change g.edist (D.map (r⁻¹ • x)) (D.map (r⁻¹ • y)) ≤ _
    rw [edist_dist, dist_eq_norm, ENNReal.coe_nnreal_eq]
    change _ ≤ ENNReal.ofReal (D.lipschitz_constant * r⁻¹) * ENNReal.ofReal ‖x - y‖
    simpa only [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
      ENNReal.ofReal_mul D.lipschitz_nonnegative, mul_assoc] using hb
  have hLipOuter : LipschitzOnWith (NNReal.mk L hL) H
      (loopDiskSet ∩ {z : LoopPlane | r ≤ ‖z‖}) := by
    intro x hx y hy
    change g.edist (H x) (H y) ≤ _
    simpa only [edist_dist, dist_eq_norm, ENNReal.ofReal_eq_coe_nnreal hL] using hLipH x hx y hy
  have hLip : LipschitzOnWith C F loopDiskSet := by
    have hp := M60.lipschitzOnWith_piecewise_of_convex (convex_closedBall (0 : LoopPlane) 1)
      (fun z : LoopPlane => ‖z‖) continuous_norm.continuousOn r hLipInner hLipOuter
      (fun z _ hz => hmatch z hz)
    have hball : closedBall (0 : LoopPlane) r = {z : LoopPlane | ‖z‖ ≤ r} := by
      ext z
      simp only [mem_closedBall, dist_zero_right, mem_ofPred_eq]
    change LipschitzOnWith C ((closedBall (0 : LoopPlane) r).piecewise
      (fun z => D.map (r⁻¹ • z)) H) loopDiskSet
    rw [hball]
    exact hp
  have hdist : ∀ x y : LoopDisk,
      g.edist (F x) (F y) ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    change edist (F x) (F y) ≤ _
    simpa only [ENNReal.ofReal_coe_nnreal, edist_dist, dist_eq_norm] using
      hLip x.property y.property
  have hsub : closedBall (0 : LoopPlane) r ⊆ loopDiskSet := closedBall_subset_closedBall hr1.le
  have hareaInner : IntegrableOn (m60AreaDensity g (fun z => D.map (r⁻¹ • z)))
      (closedBall (0 : LoopPlane) r) volume := by
    apply m60AreaDensity_integrableOn_comp_smul g D.map (inv_ne_zero hr.ne')
    rw [m60_inv_smul_closedBall hr]
    exact D.area_integrable
  obtain ⟨hint, harea⟩ := m60AreaIntegral_piecewise_closedBall g
    (fun z => D.map (r⁻¹ • z)) H r loopDiskSet
    (by simpa only [inter_eq_left.mpr hsub] using hareaInner) hareaH
  have hareaF : parametrizedRiemannianArea g F = D.area +
      ∫ z in (closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet, m60AreaDensity g H z := by
    change (∫ z in loopDiskSet, m60AreaDensity g F z) = _
    rw [harea, inter_eq_left.mpr hsub, m60AreaIntegral_rescaled_disk g D.map hr]
    rfl
  let D' : LipschitzSpanningDisk g γ' := {
    map := F
    continuous_on_disk := hLip.continuousOn
    ae_manifold_differentiable := m60_ae_mdifferentiable_of_disk_lipschitz g C.property hdist
    reparameterization := σ
    boundary_eq := by
      intro z
      have hz : (z : LoopPlane) ∉ closedBall (0 : LoopPlane) r := by
        simpa only [mem_closedBall, dist_zero_right, z.property] using not_le.mpr hr1
      exact (piecewise_eq_of_notMem _ _ _ hz).trans (hboundary z)
    lipschitz_constant := C
    lipschitz_nonnegative := C.property
    lipschitz_on_disk := hdist
    area_integrable := hint
    area_nonnegative := integral_nonneg (fun _ => Real.sqrt_nonneg _) }
  exact ⟨D', rfl, hareaF⟩

end PoincareConjecture
