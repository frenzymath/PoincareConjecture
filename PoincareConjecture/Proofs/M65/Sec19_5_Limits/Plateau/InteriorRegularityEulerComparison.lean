import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerCompetitor
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

def coordinateHalfEnergy {N : ℕ} (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (A : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N)) (z : LoopPlane) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, g.inner (X z) (A i z) (A i z)

set_option maxHeartbeats 1800000 in

theorem captured_energy_comparison {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} (he : Function.Injective e)
    {U : Set LoopPlane} (g : RiemannianMetric 3 M) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (hDU : closedBall x (2 * R) ⊆ U)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) (ball x (8 * R)))
    (ψ : EuclideanSpace ℝ (Fin 3) → M)
    (B : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin N))
    (hB : ContDiff ℝ 1 B) (CB : NNReal) (hCB : ∀ y, ‖fderiv ℝ B y‖ ≤ (CB : ℝ))
    (a : EuclideanSpace ℝ (Fin 3)) {ε : ℝ} (hε : 0 < ε)
    (hX : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (hBψ : ∀ y ∈ ball a ε, e (ψ y) = B y)
    (hvalue : (fun z => B (X.value z)) =ᵐ[volume.restrict (ball x (8 * R))]
      fun z => e (F.value z))
    (hfield : ∀ i, (fun z => fderiv ℝ B (X.value z) (X.derivative i z))
      =ᵐ[volume.restrict (ball x (8 * R))] F.derivative i)
    (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (hmetric : ∀ y ∈ ball a ε, ∀ v w : EuclideanSpace ℝ (Fin 3),
      m65EmbeddingMetric g e (ψ y) (fderiv ℝ B y v) (fderiv ℝ B y w) = gE.inner y v w)
    (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ContDiff ℝ 1 V) (CV : NNReal) (hCV : ∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ))
    (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball x R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      (∫ z in closedBall x (2 * R), coordinateHalfEnergy gE X.value X.derivative z) ≤
        ∫ z in closedBall x (2 * R), coordinateHalfEnergy gE
          (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z := by
  obtain ⟨δ0, hδ0, hcomp⟩ := exists_target_variations F x hR hDU X ψ B hB CB hCB
    a hε hX hBψ hvalue hfield V hV CV hCV φ hc hs
  obtain ⟨δ1, hδ1, hcapture⟩ := exists_variation_capture X.value V hV.continuous φ hc a hε hX
  have h28 : closedBall x (2 * R) ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have hXbig (z : LoopPlane) (hz : z ∈ ball x (8 * R)) : X.value z ∈ ball a ε :=
    ball_subset_ball (by linarith) (hX hz)
  have hold : (∫ z in closedBall x (2 * R), m65EmbeddedEnergyDensity g e F.value F.derivative z) =
      ∫ z in closedBall x (2 * R), coordinateHalfEnergy gE X.value X.derivative z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h28 hvalue,
      ae_all_iff.mpr (fun i => ae_restrict_of_ae_restrict_of_subset h28 (hfield i)),
      ae_restrict_mem measurableSet_closedBall] with z hv hd hz
    have hq : F.value z = ψ (X.value z) :=
      he (hv.symm.trans (hBψ _ (hXbig z (h28 hz))).symm)
    simp only [m65EmbeddedEnergyDensity, coordinateHalfEnergy, hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hd i]
    exact hmetric _ (hXbig z (h28 hz)) _ _
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, ?_⟩
  intro t ht
  obtain ⟨H, hin, hout⟩ := hcomp t (lt_of_lt_of_le ht (min_le_left _ _))
  have hext : H.value =ᵐ[volume.restrict (closedBall x (2 * R))ᶜ] F.value :=
    (ae_restrict_mem measurableSet_closedBall.compl).mono (fun z hz => (hout z hz).1)
  have hm := hmin x (2 * R) (by positivity) hDU H
    (ae_restrict_of_ae_restrict_of_subset (sdiff_subset_compl U (closedBall x (2 * R))) hext)
  have hnew : (∫ z in closedBall x (2 * R), m65EmbeddedEnergyDensity g e H.value H.derivative z) =
      ∫ z in closedBall x (2 * R), coordinateHalfEnergy gE
        (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro z hz
    simp only [m65EmbeddedEnergyDensity, coordinateHalfEnergy, (hin z hz).1, (hin z hz).2]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hmetric _ (hcapture t (lt_of_lt_of_le ht (min_le_right _ _)) (h28 hz)) _ _
  rwa [hold, hnew] at hm

end PoincareConjecture.M65Euler
