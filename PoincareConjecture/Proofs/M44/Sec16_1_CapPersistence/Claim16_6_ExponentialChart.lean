import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_ExponentialConvergence
import PoincareConjecture.Proofs.M44.Mathlib.SmoothChartInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

namespace NormalizedCapExponential

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
  {Q : SurgeryCapClose g₀ S g tip scale eta}

theorem coordinateMap_fderiv (D : NormalizedCapExponential Q R)
    {x : E} (hx : x ∈ ball 0 R) :
    fderiv ℝ D.coordinateMap x =
      (mfderiv (𝓡 3) (𝓡 3) Q.inverse (D.map x)).comp (mfderiv (𝓡 3) (𝓡 3) D.map x) := by
  have hf := (D.smooth.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have hi := (Q.inverse_smooth.contMDiffAt
    (Q.toPartialDiffeomorph.open_target.mem_nhds (D.map_mem x hx))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) x hi hf
  rw [mfderiv_eq_fderiv] at hd
  exact hd

end NormalizedCapExponential

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)

theorem eventually_bijective_mfderiv_initial_exponentials
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {K : Set E} (hK : IsCompact K)
    (hKR : K ⊆ ball 0 (R / 2)) :
    ∀ᶠ n in atTop, ∀ x ∈ K, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (D n).map x) := by
  have hder := tendstoUniformlyOn_fderiv_adjusted_exponentials
    g₀ S g tip scale eta Q D heta L hL hK hKR
  filter_upwards [hder.eventually_bijective_of_tendsto_id] with n hn
  intro x hx
  have hxR : x ∈ ball (0 : E) R :=
    (ball_subset_ball (by linarith [(D 0).radius_pos])) (hKR hx)
  have hcoord := ((D n).coordinateMap_smooth.contDiffAt
    (isOpen_ball.mem_nhds hxR)).differentiableAt (by simp)
  have hcomp := fderiv_comp x
    ((standardFrameLogarithm_contDiff g₀ L).differentiable (by simp) _) hcoord
  rw [(D n).coordinateMap_fderiv hxR] at hcomp
  let A : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) (D n).map x
  have hinj : Function.Injective A := by
    intro v w hvw
    apply (hn x hx).1
    rw [hcomp]
    change fderiv ℝ (standardFrameLogarithm g₀ L) ((D n).coordinateMap x)
        (mfderiv (𝓡 3) (𝓡 3) (Q n).inverse ((D n).map x) (A v)) =
      fderiv ℝ (standardFrameLogarithm g₀ L) ((D n).coordinateMap x)
        (mfderiv (𝓡 3) (𝓡 3) (Q n).inverse ((D n).map x) (A w))
    rw [hvw]
  change Function.Bijective A
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := A.toLinearMap) rfl).mp hinj⟩

theorem eventually_initial_exponential_charts
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {r : ℝ} (hr : 0 < r) (hrR : r < R / 2) :
    ∀ᶠ n in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E (S n).carrier ∞,
      (e : E → (S n).carrier) = (D n).map ∧
      e.source = ball 0 r ∧ e.target = (D n).map '' ball 0 r := by
  have hKR : closedBall (0 : E) r ⊆ ball 0 (R / 2) := closedBall_subset_ball hrR
  have hinj := eventually_injOn_initial_exponentials g₀ S g tip scale eta Q D heta L hL
    (isCompact_closedBall 0 r) (convex_closedBall 0 r) hKR
  have hD := eventually_bijective_mfderiv_initial_exponentials
    g₀ S g tip scale eta Q D heta L hL (isCompact_closedBall 0 r) hKR
  filter_upwards [hinj, hD] with n hn hd
  have hrR' : r ≤ R := by linarith
  exact ⟨Poincare.partialDiffeomorphOfInjOn (D n).map (ball 0 r) isOpen_ball
    ((D n).smooth.mono (ball_subset_ball hrR')) (hn.mono ball_subset_closedBall)
    (fun x hx => hd x (ball_subset_closedBall hx)), rfl, rfl, rfl⟩

end PoincareConjecture.M44
