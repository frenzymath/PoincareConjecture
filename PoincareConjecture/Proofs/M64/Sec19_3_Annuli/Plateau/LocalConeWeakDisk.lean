import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeWeakExtraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedTangentProjection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingKernelWeakClosure
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy












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
local notation "S" => ball (0 : LoopPlane) 1
local notation "mu" => volume.restrict S



theorem m64ContinuousDisk_observed_weak_columns
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (f : ℕ → LoopPlane → M),
      (∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j)) → ∀ F : LoopPlane → M,
        Continuous F → (∀ p, Tendsto (fun j => f j p) atTop (𝓝 (F p))) →
        ∀ (b : ℕ → ℝ) (B : ℝ), Tendsto b atTop (𝓝 B) →
          (∀ j, (∫ p in loopDiskSet, m60EnergyDensity g (f j) p) ≤ b j) →
          let u := fun j => e ∘ f j
          let D := fun j i p => fderiv ℝ (u j) p (EuclideanSpace.single i 1)
          ∃ (hu : ∀ j, MemLp (u j) 2 mu) (hF : MemLp (e ∘ F) 2 mu)
            (hD : ∀ j i, MemLp (D j i) 2 mu) (k : ℕ → ℕ) (W : Fin 2 → Lp E 2 mu),
            StrictMono k ∧
            Tendsto (fun j => (hu (k j)).toLp (u (k j))) atTop (𝓝 (hF.toLp (e ∘ F))) ∧
            (∀ i, WeakConverges (fun j => (hD (k j) i).toLp (D (k j) i)) (W i)) ∧
            (∀ i, ∀ᵐ p ∂mu, W i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F p))) ∧
            (∀ i a, HasWeakPartialDeriv i (fun p => W i p a) (fun p => e (F p) a) S) ∧
            ∀ i, ‖W i‖ ^ 2 ≤ Q * B := by
  obtain ⟨Q, hQ, hcolumn⟩ := M60.exists_observed_derivative_energy_bound g e he
  refine ⟨Q, hQ, ?_⟩
  intro f hf F hFc hpoint b B hb henergy u D
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall (0 : LoopPlane) 1).measure_lt_top⟩
  have huc (j : ℕ) : ContDiff ℝ 1 (u j) := contMDiff_iff_contDiff.mp (he.comp (hf j))
  have hDc (j : ℕ) (i : Fin 2) : Continuous (D j i) :=
    ((huc j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hu (j : ℕ) : MemLp (u j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (huc j).continuous.aestronglyMeasurable).mpr
    exact ((huc j).continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hF : MemLp (e ∘ F) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm
      (he.continuous.comp hFc).aestronglyMeasurable).mpr
    exact ((he.continuous.comp hFc).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hD (j : ℕ) (i : Fin 2) : MemLp (D j i) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hDc j i).aestronglyMeasurable).mpr
    exact ((hDc j i).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hDi (j : ℕ) (i : Fin 2) : IntegrableOn (fun p => ‖D j i p‖ ^ 2) S volume :=
    (memLp_two_iff_integrable_sq_norm (hDc j i).aestronglyMeasurable).mp (hD j i)
  have hcolint (j : ℕ) (i : Fin 2) : (∫ p in S, ‖D j i p‖ ^ 2) ≤ Q * b j := by
    have hEi : IntegrableOn (m60EnergyDensity g (f j)) loopDiskSet volume :=
      (m60EnergyDensity_continuous g (hf j)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : LoopPlane) 1)
    calc
      _ ≤ ∫ p in S, Q * m60EnergyDensity g (f j) p := by
        apply integral_mono (hDi j i) ((hEi.mono_set ball_subset_closedBall).const_mul Q)
        intro p
        simpa only [D, u, EuclideanSpace.basisFun_apply] using hcolumn (f j) (hf j) p i
      _ = Q * ∫ p in S, m60EnergyDensity g (f j) p := integral_const_mul _ _
      _ ≤ Q * ∫ p in loopDiskSet, m60EnergyDensity g (f j) p :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hEi
          (Eventually.of_forall (m60EnergyDensity_nonneg g (f j)))
          (Eventually.of_forall fun p hp => ball_subset_closedBall hp)) hQ
      _ ≤ Q * b j := mul_le_mul_of_nonneg_left (henergy j) hQ
  obtain ⟨R, hR⟩ := hb.cauchySeq.isBounded_range.exists_norm_le
  have hbR (j : ℕ) : b j ≤ max R 0 :=
    (le_abs_self _).trans ((hR _ (mem_range_self j)).trans (le_max_left _ _))
  obtain ⟨k, W, hk, hweak⟩ := m64Plane_two_columns_subsequence D hD
    (fun j i => (hcolint j i).trans (mul_le_mul_of_nonneg_left (hbR j) hQ))
  obtain ⟨A, hA⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hvalbound (j : ℕ) (p : LoopPlane) : ‖u j p‖ ≤ max A 0 :=
    (hA _ (mem_range_self (f j p))).trans (le_max_left _ _)
  have hstrong := m64Bounded_pointwise_l2_tendsto u (e ∘ F) hu hF
    (le_max_right A 0) hvalbound (Eventually.of_forall fun p =>
      (he.continuous.tendsto (F p)).comp (hpoint p))
  have hstrongk := hstrong.comp hk.tendsto_atTop
  have hvalueweak : WeakConverges (fun j => (hu (k j)).toLp (u (k j))) (hF.toLp (e ∘ F)) :=
    fun L => (L.continuous.tendsto _).comp hstrongk
  have htangent (j : ℕ) (i : Fin 2) (p : LoopPlane) :
      D j i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f j p)) := by
    refine ⟨mfderiv (𝓡 2) (𝓡 n) (f j) p (EuclideanSpace.single i 1), ?_⟩
    have hc := mfderiv_comp p (he.mdifferentiable (by simp) _)
      ((hf j).mdifferentiable (by simp) _)
    have hd := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
    rw [mfderiv_eq_fderiv] at hd
    exact hd.symm
  refine ⟨hu, hF, hD, k, W, hk, hstrongk, hweak, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨P, K, hP, hK, hPbound, hfix, hrange⟩ :=
      m64ChartReadable_tangent_projection e he hread
    let Rj := fun j p => ContinuousLinearMap.id ℝ E - P (f (k j) p)
    let R0 := fun p => ContinuousLinearMap.id ℝ E - P (F p)
    have hRj (j : ℕ) : AEStronglyMeasurable (Rj j) mu :=
      (continuous_const.sub (hP.comp (hf (k j)).continuous)).aestronglyMeasurable
    have hRb (j : ℕ) : ∀ᵐ p ∂mu, ‖Rj j p‖ ≤ 1 + K := Eventually.of_forall fun p =>
      (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hPbound _))
    have hRlim : ∀ᵐ p ∂mu, Tendsto (fun j => Rj j p) atTop (𝓝 (R0 p)) :=
      Eventually.of_forall fun p => tendsto_const_nhds.sub
        ((hP.tendsto (F p)).comp ((hpoint p).comp hk.tendsto_atTop))
    have hz (j : ℕ) : ∀ᵐ p ∂mu, Rj j p ((hD (k j) i).toLp (D (k j) i) p) = 0 := by
      filter_upwards [(hD (k j) i).coeFn_toLp] with p hp
      rw [hp]
      obtain ⟨v, hv⟩ := htangent (k j) i p
      change D (k j) i p - P (f (k j) p) (D (k j) i p) = 0
      rw [← hv, hfix, sub_self]
    have hzlim := m64MovingKernel_weak_closed Rj R0 hRj (by positivity : 0 ≤ 1 + K)
      hRb hRlim (hweak i) hz
    filter_upwards [hzlim] with p hp
    change W i p - P (F p) (W i p) = 0 at hp
    have hfixed : P (F p) (W i p) = W i p := (sub_eq_zero.mp hp).symm
    simpa only [hfixed] using hrange (F p) (W i p)
  · intro i a
    have hseq (j : ℕ) : HasWeakPartialDeriv i
        (fun p => (hD (k j) i).toLp (D (k j) i) p a)
        (fun p => (hu (k j)).toLp (u (k j)) p a) S :=
      m64WeakPartialDeriv_ae_congr
        ((hu (k j)).coeFn_toLp.symm.mono fun p hp => congrArg (fun v : E => v a) hp)
        ((hD (k j) i).coeFn_toLp.symm.mono fun p hp => congrArg (fun v : E => v a) hp)
        (m64Plane_c1_weak_partial isOpen_ball (huc (k j)) i a)
    exact m64WeakPartialDeriv_ae_congr
      (hF.coeFn_toLp.mono fun p hp => congrArg (fun v : E => v a) hp)
      EventuallyEq.rfl (m64Plane_weak_partial_closed hvalueweak (hweak i) i a hseq)
  · intro i
    apply m64Weak_limit_norm_sq_le (hweak i) ((hb.comp hk.tendsto_atTop).const_mul Q)
    intro j
    calc
      _ = ∫ p in S, ‖D (k j) i p‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
        exact integral_congr_ae ((hD (k j) i).coeFn_toLp.mono fun p hp =>
          congrArg (fun v : E => ‖v‖ ^ 2) hp)
      _ ≤ Q * b (k j) := hcolint (k j) i

end PoincareConjecture
