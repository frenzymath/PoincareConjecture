import PoincareConjecture.Proofs.M08.ContinuationCurve
import PoincareConjecture.Proofs.M08.ManifoldEndpointExtension
import PoincareConjecture.Proofs.M08.SqrtRecovery
import PoincareConjecture.Proofs.M08.VariationAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem continuationAction_intervalIntegrable {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hIU : Icc a b ⊆ U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) :
    IntervalIntegrable (regularizedLIntegrand F T α) volume a b := by
  have hαI := hα.mono hIU
  have hA := (contMDiffOn_mfderiv_const_apply hU α hα (1 : ℝ)).mono hIU
  have ht : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ ↦ T - s ^ 2) (Icc a b) :=
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
  have hg := (movingMetric_pair_contMDiffOn F (fun s : ℝ ↦ T - s ^ 2) α
    (curveVelocity (n := n) α) (curveVelocity (n := n) α) ht hαI hA hA htime).contDiffOn
  have hR := ((hM04.scalar_regular n M J F).comp (ht.prodMk hαI)
    (fun s hs ↦ ⟨htime s hs, mem_univ _⟩)).contDiffOn
  have hL : ContDiffOn ℝ ∞ (regularizedLIntegrand F T α) (Icc a b) :=
    ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hR).add (contDiffOn_const.mul hg)
  exact hL.continuousOn.intervalIntegrable_of_Icc hab

set_option maxHeartbeats 1200000 in

theorem exists_backward_geodesic_of_continuation {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax τ₂ : ℝ)
    (hτ₂ : 0 < τ₂) (hmax : τ₂ ≤ τmax) (hwindow : Icc (T - τmax) T ⊆ J)
    (α : ℝ → M)
    (hclosed : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc 0 (Real.sqrt τ₂)))
    (hα : IsContinuationCurve F T α (Ioo 0 (Real.sqrt τ₂))) :
    ∃ q : BackwardTimePath F T 0 τ₂,
      EqOn q.curve (fun τ ↦ α (Real.sqrt τ)) (Icc 0 τ₂) ∧
      IsBackwardLGeodesic F T 0 τ₂ q := by
  have hroot : 0 < Real.sqrt τ₂ := Real.sqrt_pos.mpr hτ₂
  have hT : T ∈ J := hwindow ⟨sub_le_self T (hτ₂.le.trans hmax), le_rfl⟩
  have htime (τ : ℝ) (hτ : τ ∈ Icc 0 τ₂) : T - τ ∈ J :=
    hwindow ⟨sub_le_sub_left (hτ.2.trans hmax) T, sub_le_self T hτ.1⟩
  have htimeSq (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt τ₂)) : T - s ^ 2 ∈ J := by
    apply htime
    refine ⟨sq_nonneg s, ?_⟩
    simpa only [Real.sq_sqrt hτ₂.le] using
      (sq_le_sq₀ hs.1 (Real.sqrt_nonneg τ₂)).mpr hs.2
  obtain ⟨β, U, hU, hIU, hβ, hβα⟩ := exists_smooth_manifold_extension_Icc hroot α hclosed
  have hcont : ContinuousOn β (Icc (Real.sqrt 0) (Real.sqrt τ₂)) := by
    simpa only [Real.sqrt_zero] using (hβ.mono hIU).continuousOn
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 β (Ioo (Real.sqrt 0) (Real.sqrt τ₂)) := by
    simpa only [Real.sqrt_zero] using
      (hβ.of_le (by simp)).mono (Ioo_subset_Icc_self.trans hIU)
  have hint : IntervalIntegrable (regularizedLIntegrand F T β) volume
      (Real.sqrt 0) (Real.sqrt τ₂) := by
    simpa only [Real.sqrt_zero] using
      continuationAction_intervalIntegrable F hM04 T hroot.le hU hIU β hβ htimeSq
  let q := backwardPathOfSqrt F T 0 τ₂ le_rfl hτ₂ hT htime β hcont hreg hint
  have hagree : EqOn q.curve (fun τ ↦ α (Real.sqrt τ)) (Icc 0 τ₂) := by
    intro τ hτ
    exact hβα ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hτ.2⟩
  have hsquare : EqOn (squareReparameterizedCurve q.curve) α (Ioo 0 (Real.sqrt τ₂)) := by
    intro s hs
    change β (Real.sqrt (s ^ 2)) = α s
    rw [Real.sqrt_sq hs.1.le]
    exact hβα (Ioo_subset_Icc_self hs)
  have hphase : IsContinuationCurve F T (squareReparameterizedCurve q.curve)
      (Ioo (Real.sqrt 0) (Real.sqrt τ₂)) := by
    simpa only [Real.sqrt_zero] using hα.congr isOpen_Ioo hsquare
  have htimeInterior (s : ℝ) (hs : s ∈ Ioo (Real.sqrt 0) (Real.sqrt τ₂)) :
      T - s ^ 2 ∈ interior J :=
    backwardSquareTime_mem_interior hwindow le_rfl hτ₂ hmax hs
  obtain ⟨E, hE⟩ := continuationCurve_regularizedEuler F hM04 T isOpen_Ioo hphase htimeInterior
  exact ⟨q, hagree, isBackwardLGeodesic_of_regularizedEuler_extension hM04 q E hE⟩

end PoincareConjecture.M08
