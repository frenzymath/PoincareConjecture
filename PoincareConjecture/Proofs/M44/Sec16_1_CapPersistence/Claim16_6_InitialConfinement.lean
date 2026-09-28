import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ChartTopology
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_MetricBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_LengthBarrier
import PoincareConjecture.Proofs.M01.NormalizationScaling










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SurgeryCapClose

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}

set_option backward.isDefEq.respectTransparency false in


theorem inverse_quadratic_bound (Q : SurgeryCapClose g₀ S g tip scale eta)
    {y : S.carrier} (hy : y ∈ Q.map '' g₀.metric.ball 0 eta⁻¹)
    (w : TangentSpace (𝓡 3) y) :
    (scale ^ 2 * (1 - eta)) * g₀.metric.inner (Q.inverse y)
        (mfderiv (𝓡 3) (𝓡 3) Q.inverse y w)
        (mfderiv (𝓡 3) (𝓡 3) Q.inverse y w) ≤ g.inner y w w := by
  let e := Q.toPartialDiffeomorph
  have hD : e.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hd := hD.comp_symm_deriv hy
  have hcancel : mfderiv (𝓡 3) (𝓡 3) Q.map (Q.inverse y)
      (mfderiv (𝓡 3) (𝓡 3) Q.inverse y w) = w :=
    congrArg (fun L => L w) hd
  have hx : Q.inverse y ∈ g₀.metric.ball 0 eta⁻¹ := e.map_target hy
  have hb := (Q.quadratic_bounds hx (mfderiv (𝓡 3) (𝓡 3) Q.inverse y w)).1
  rw [hcancel, Q.right_inverse hy] at hb
  calc
    _ = scale ^ 2 * ((1 - eta) * g₀.metric.inner (Q.inverse y)
        (mfderiv (𝓡 3) (𝓡 3) Q.inverse y w)
        (mfderiv (𝓡 3) (𝓡 3) Q.inverse y w)) := by ring
    _ ≤ scale ^ 2 * (scale⁻¹ ^ 2 * g.inner y w w) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg scale)
    _ = g.inner y w w := by field_simp [Q.scale_pos.ne']



theorem ball_subset_image_of_buffer
    (Q : SurgeryCapClose g₀ S g tip scale eta) (heta : eta < 1)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    g.ball tip (Real.sqrt (scale ^ 2 * (1 - eta)) * r) ⊆
      Q.map '' g₀.metric.ball 0 r := by
  let c := scale ^ 2 * (1 - eta)
  have hc : 0 < c := mul_pos (sq_pos_of_pos Q.scale_pos) (sub_pos.mpr heta)
  let k := m01RescaledMetric g₀.metric c hc
  let e := Q.toPartialDiffeomorph
  have hsub : g₀.metric.ball 0 r ⊆ e.source := fun _ hx =>
    hx.trans_le (ENNReal.ofReal_le_ofReal hrEta.le)
  have hopen : IsOpen (g₀.metric.ball 0 r) := by
    rw [M36.standard_ball_eq_euclidean g₀ hr]
    exact Metric.isOpen_ball
  have hU : IsOpen (Q.map '' g₀.metric.ball 0 r) :=
    e.toOpenPartialHomeomorph.isOpen_image_of_subset_source hopen hsub
  have hzero : (0 : StandardCapSpace) ∈ g₀.metric.ball 0 r := by
    rw [M36.standard_ball_eq_euclidean g₀ hr]
    exact Metric.mem_ball_self ((M36.radialEuclideanRadius_pos_iff g₀ r).mpr hr)
  have htip : tip ∈ Q.map '' g₀.metric.ball 0 r := ⟨0, hzero, Q.map_tip⟩
  have hclsub : closure (Q.map '' g₀.metric.ball 0 r) ⊆ e.target := by
    rw [Q.closure_image_ball hr hrEta]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem Q.map
      (hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr hrEta))
  have hinvtip : Q.inverse tip = 0 := by
    exact (congrArg Q.inverse Q.map_tip.symm).trans (Q.left_inverse (hsub hzero))
  apply g.ball_subset_of_inverse_length_barrier k Q.inverse hU htip
  · intro y hy
    exact (e.symm.contMDiffOn y (hclsub hy)).contMDiffAt
      (e.open_target.mem_nhds (hclsub hy))
  · intro y hy w
    exact Q.inverse_quadratic_bound (hclsub hy) w
  · intro y hy
    rw [Q.frontier_image_ball hr hrEta] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxsource : x ∈ g₀.metric.ball 0 eta⁻¹ := by
      change g₀.metric.edist 0 x < ENNReal.ofReal eta⁻¹
      rw [hx]
      exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr hrEta
    change ENNReal.ofReal (Real.sqrt c * r) ≤
      (m01RescaledMetric g₀.metric c hc).edist (Q.inverse tip) (Q.inverse (Q.map x))
    rw [hinvtip, Q.left_inverse hxsource, m01RescaledMetric_edist, hx,
      ENNReal.ofReal_mul (Real.sqrt_nonneg c)]




theorem isCompact_closure_ball_of_buffer
    (Q : SurgeryCapClose g₀ S g tip scale eta) (heta : eta < 1)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    IsCompact (closure (g.ball tip (Real.sqrt (scale ^ 2 * (1 - eta)) * r))) := by
  have hcompact : IsCompact (closure (Q.map '' g₀.metric.ball 0 r)) := by
    rw [Q.closure_image_ball hr hrEta]
    apply (M36.standard_closed_ball_compact g₀ hr.le).image_of_continuousOn
    apply Q.map_smooth.continuousOn.mono
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr hrEta)
  exact hcompact.of_isClosed_subset isClosed_closure
    (closure_mono (Q.ball_subset_image_of_buffer heta hr hrEta))

end PoincareConjecture.SurgeryCapClose
