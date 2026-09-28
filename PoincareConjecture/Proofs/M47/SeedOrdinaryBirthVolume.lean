import PoincareConjecture.Proofs.M47.SeedVolumeTransport
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_ordinary_slice_chart
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (U : TopologicalSpace.Opens C.carrier)
    (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I) (q : U) :
    ∃ chart : PartialDiffeomorph (𝓡 3) (𝓡 3) U (F.slice (origin + s / scale)).carrier ∞,
      chart.source = univ ∧ ∀ y : U, chart y = e.forward s hs y.val := by
  let inclusion := U.openPartialHomeomorphSubtypeCoe ⟨q⟩
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inclusion.symm inclusion.target := by
    intro p hp
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U inclusion.symm inclusion.target p).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hp
    intro x hx
    exact inclusion.right_inv hx
  let inclusionDiff : PartialDiffeomorph (𝓡 3) (𝓡 3) U C.carrier ∞ := {
    toPartialEquiv := inclusion.toPartialEquiv
    open_source := inclusion.open_source
    open_target := inclusion.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi }
  let chart := inclusionDiff.trans (M44.cylinderSliceChart e U.isOpen s hs)
  refine ⟨chart, ?_, fun _ => rfl⟩
  ext y
  change (y ∈ (univ : Set U) ∧ y.val ∈ U) ↔ y ∈ (univ : Set U)
  simp only [mem_univ, y.property, and_self]

theorem seed_ordinary_birth_volume
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (U : TopologicalSpace.Opens C.carrier)
    [CompactSpace U]
    (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I)
    (g : RiemannianMetric 3 U)
    (hmetric : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w))
    (q : U) {R V : ℝ} (hR : 0 < R)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (origin + s / scale))
      ((F.metric (origin + s / scale)).ball (e.forward s hs q.val) (R / 2))) :
    ENNReal.ofReal (V / 8) ≤ calibratedMetricVolume g (g.ball q R) := by
  obtain ⟨chart, hsource, hchart⟩ := exists_seed_ordinary_slice_chart U e s hs q
  have hmap : (chart : U → (F.slice (origin + s / scale)).carrier) =
      fun y : U => e.forward s hs y.val := funext hchart
  have hnonnegative (y : U) (v : TangentSpace (𝓡 3) y) : 0 ≤ g.inner y v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos y v hv).le
  have hpull (y : U) (v w : TangentSpace (𝓡 3) y) :
      g.inner y v w = (F.metric (origin + s / scale)).inner (chart y)
        (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y w) := by
    have heq := congrArg (fun f : U → (F.slice (origin + s / scale)).carrier =>
      (F.metric (origin + s / scale)).inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w)) hmap
    exact (hmetric y v w).trans heq.symm
  have hlower : ∀ y ∈ chart.source, ∀ v : TangentSpace (𝓡 3) y,
      g.inner y v v ≤ 4 * (F.metric (origin + s / scale)).inner (chart y)
        (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y v) := by
    intro y _hy v
    rw [← hpull]
    nlinarith [hnonnegative y v]
  have hupper : ∀ y ∈ chart.source, ∀ v : TangentSpace (𝓡 3) y,
      (F.metric (origin + s / scale)).inner (chart y)
        (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y v) ≤
          4 * g.inner y v v := by
    intro y _hy v
    rw [← hpull]
    nlinarith [hnonnegative y v]
  have hcompare := seed_target_ball_volume_le_source g (F.metric (origin + s / scale))
    chart hlower hupper q hR isClosed_closure.isCompact
      (by rw [hsource]; exact subset_univ _)
  rw [hchart] at hcompare
  have hbound := hvolume.trans hcompare
  calc
    ENNReal.ofReal (V / 8) = ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal V := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) * (8 * calibratedMetricVolume g (g.ball q R)) :=
      mul_le_mul_right hbound _
    _ = calibratedMetricVolume g (g.ball q R) := by
      rw [← mul_assoc]
      have hcancel : ENNReal.ofReal (1 / 8 : ℝ) * 8 = 1 := by
        rw [← show ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        norm_num
      rw [hcancel, one_mul]

end PoincareConjecture.Proofs.M47
