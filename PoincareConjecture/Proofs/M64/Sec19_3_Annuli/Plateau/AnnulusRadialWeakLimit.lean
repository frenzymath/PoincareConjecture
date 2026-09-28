import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeWeakDisk
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTargetCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)

set_option maxHeartbeats 800000 in

theorem m64ObservedContinuousDisk_weak_limit
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (a : LoopPlane) (r : ℝ)
    (f : ℕ → LoopPlane → M) (F : LoopPlane → M)
    (hf : ∀ j, ContinuousOn (f j) (closedBall a r)) (hF : ContinuousOn F (closedBall a r))
    (hpoint : ∀ x ∈ ball a r, Tendsto (fun j => f j x) atTop (𝓝 (F x)))
    (V : ℕ → Fin 2 → LoopPlane → E)
    (hV : ∀ j i, MemLp (V j i) 2 (volume.restrict (ball a r)))
    (hw : ∀ j i b, HasWeakPartialDeriv i (fun x => V j i x b)
      (fun x => e (f j x) b) (ball a r))
    (ht : ∀ j i, ∀ᵐ x ∂volume.restrict (ball a r),
      V j i x ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f j x)))
    (b : ℕ → ℝ) {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ j i, (∫ x in ball a r, ‖V j i x‖ ^ 2) ≤ b j) :
    ∃ (hu : ∀ j, MemLp (e ∘ f j) 2 (volume.restrict (ball a r)))
      (hU : MemLp (e ∘ F) 2 (volume.restrict (ball a r)))
      (k : ℕ → ℕ) (W : Fin 2 → Lp E 2 (volume.restrict (ball a r))),
      StrictMono k ∧
      Tendsto (fun j => (hu (k j)).toLp (e ∘ f (k j))) atTop (𝓝 (hU.toLp (e ∘ F))) ∧
      (∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i)) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (ball a r),
        W i x ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F x))) ∧
      (∀ i c, HasWeakPartialDeriv i (fun x => W i x c) (fun x => e (F x) c) (ball a r)) ∧
      ∀ i, ‖W i‖ ^ 2 ≤ B := by
  let S := ball a r
  let mu := volume.restrict S
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top⟩
  have huc (j : ℕ) : ContinuousOn (e ∘ f j) (closedBall a r) :=
    he.continuous.comp_continuousOn (hf j)
  have hUc : ContinuousOn (e ∘ F) (closedBall a r) := he.continuous.comp_continuousOn hF
  have hu (j : ℕ) : MemLp (e ∘ f j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm
      (((huc j).mono ball_subset_closedBall).aestronglyMeasurable isOpen_ball.measurableSet)).mpr
    exact ((huc j).norm.pow 2).integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set ball_subset_closedBall
  have hU : MemLp (e ∘ F) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm
      ((hUc.mono ball_subset_closedBall).aestronglyMeasurable isOpen_ball.measurableSet)).mpr
    exact (hUc.norm.pow 2).integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set ball_subset_closedBall
  obtain ⟨C, hC⟩ := hb.cauchySeq.isBounded_range.exists_norm_le
  have hbC (j : ℕ) : b j ≤ C := (le_abs_self _).trans (hC _ (mem_range_self j))
  obtain ⟨k, W, hk, hweak⟩ := m64Plane_two_columns_subsequence V hV
    (fun j i => (hbound j i).trans (hbC j))
  obtain ⟨D, hD⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hvalbound (j : ℕ) (x : LoopPlane) : ‖e (f j x)‖ ≤ max D 0 :=
    (hD _ (mem_range_self (f j x))).trans (le_max_left _ _)
  have hpobs : ∀ᵐ x ∂mu, Tendsto (fun j => e (f j x)) atTop (𝓝 (e (F x))) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (he.continuous.tendsto (F x)).comp (hpoint x hx)
  have hstrong := m64Bounded_pointwise_l2_tendsto
    (fun j => e ∘ f j) (e ∘ F) hu hU (le_max_right D 0) hvalbound hpobs
  have hstrongk := hstrong.comp hk.tendsto_atTop
  have hvalueweak : WeakConverges (fun j => (hu (k j)).toLp (e ∘ f (k j))) (hU.toLp (e ∘ F)) :=
    fun L => (L.continuous.tendsto _).comp hstrongk
  refine ⟨hu, hU, k, W, hk, hstrongk, hweak, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨P, K, hP, hK, hPbound, hfix, hrange⟩ :=
      m64ChartReadable_tangent_projection e he hread
    let Rj := fun j x => ContinuousLinearMap.id ℝ E - P (f (k j) x)
    let R0 := fun x => ContinuousLinearMap.id ℝ E - P (F x)
    have hRj (j : ℕ) : AEStronglyMeasurable (Rj j) mu :=
      (continuous_const.continuousOn.sub
        (hP.comp_continuousOn ((hf (k j)).mono ball_subset_closedBall))).aestronglyMeasurable
          isOpen_ball.measurableSet
    have hRb (j : ℕ) : ∀ᵐ x ∂mu, ‖Rj j x‖ ≤ 1 + K := Eventually.of_forall fun x =>
      (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hPbound _))
    have hRlim : ∀ᵐ x ∂mu, Tendsto (fun j => Rj j x) atTop (𝓝 (R0 x)) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact tendsto_const_nhds.sub ((hP.tendsto (F x)).comp ((hpoint x hx).comp hk.tendsto_atTop))
    have hz (j : ℕ) : ∀ᵐ x ∂mu, Rj j x ((hV (k j) i).toLp (V (k j) i) x) = 0 := by
      filter_upwards [(hV (k j) i).coeFn_toLp, ht (k j) i] with x hx htx
      rw [hx]
      obtain ⟨v, hv⟩ := htx
      change V (k j) i x - P (f (k j) x) (V (k j) i x) = 0
      rw [← hv, hfix, sub_self]
    have hzlim := m64MovingKernel_weak_closed Rj R0 hRj (by positivity : 0 ≤ 1 + K)
      hRb hRlim (hweak i) hz
    filter_upwards [hzlim] with x hx
    change W i x - P (F x) (W i x) = 0 at hx
    have hfixed : P (F x) (W i x) = W i x := (sub_eq_zero.mp hx).symm
    simpa only [hfixed] using hrange (F x) (W i x)
  · intro i c
    have hseq (j : ℕ) : HasWeakPartialDeriv i
        (fun x => (hV (k j) i).toLp (V (k j) i) x c)
        (fun x => (hu (k j)).toLp (e ∘ f (k j)) x c) S :=
      m64WeakPartialDeriv_ae_congr
        ((hu (k j)).coeFn_toLp.symm.mono fun x hx => congrArg (fun v : E => v c) hx)
        ((hV (k j) i).coeFn_toLp.symm.mono fun x hx => congrArg (fun v : E => v c) hx)
        (hw (k j) i c)
    exact m64WeakPartialDeriv_ae_congr
      (hU.coeFn_toLp.mono fun x hx => congrArg (fun v : E => v c) hx)
      EventuallyEq.rfl (m64Plane_weak_partial_closed hvalueweak (hweak i) i c hseq)
  · intro i
    apply m64Weak_limit_norm_sq_le (hweak i) (hb.comp hk.tendsto_atTop)
    intro j
    calc
      _ = ∫ x in ball a r, ‖V (k j) i x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
        exact integral_congr_ae ((hV (k j) i).coeFn_toLp.mono fun x hx =>
          congrArg (fun v : E => ‖v‖ ^ 2) hx)
      _ ≤ b (k j) := hbound (k j) i

end PoincareConjecture
