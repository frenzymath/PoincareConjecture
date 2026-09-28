import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerFields
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerGluing
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerReconstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

set_option maxHeartbeats 1800000 in

theorem exists_target_variations {M : Type u} {N K : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (hDU : closedBall x (2 * R) ⊆ U)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin K) => y) (ball x (8 * R)))
    (ψ : EuclideanSpace ℝ (Fin K) → M)
    (B : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin N))
    (hB : ContDiff ℝ 1 B) (CB : NNReal) (hCB : ∀ y, ‖fderiv ℝ B y‖ ≤ (CB : ℝ))
    (a : EuclideanSpace ℝ (Fin K)) {ε : ℝ} (hε : 0 < ε)
    (hX : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (hBψ : ∀ y ∈ ball a ε, e (ψ y) = B y)
    (hvalue : (fun z => B (X.value z)) =ᵐ[volume.restrict (ball x (8 * R))]
      fun z => e (F.value z))
    (hfield : ∀ i, (fun z => fderiv ℝ B (X.value z) (X.derivative i z))
      =ᵐ[volume.restrict (ball x (8 * R))] F.derivative i)
    (V : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (hV : ContDiff ℝ 1 V) (CV : NNReal) (hCV : ∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ))
    (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball x R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∃ H : M65LocalWeakMap e U,
      (∀ z ∈ closedBall x (2 * R),
        H.value z = ψ (variationValue X.value V φ t z) ∧
          ∀ i, H.derivative i z = fderiv ℝ B (variationValue X.value V φ t z)
            (variationField X.value X.derivative V φ t i z)) ∧
      ∀ z ∉ closedBall x (2 * R), H.value z = F.value z ∧
        ∀ i, H.derivative i z = F.derivative i z := by
  obtain ⟨δ, hδ, hcapture⟩ := exists_variation_capture X.value V hV.continuous φ hc a hε hX
  have h68 : closedBall x (6 * R) ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have h46 : closedBall x (4 * R) ⊆ ball x (6 * R) := closedBall_subset_ball (by linarith)
  have h24 : closedBall x (2 * R) ⊆ ball x (4 * R) := closedBall_subset_ball (by linarith)
  have h48 : ball x (4 * R) ⊆ ball x (8 * R) := ball_subset_ball (by linarith)
  have h28 := h24.trans h48
  have hφ6 : tsupport φ ⊆ ball x (6 * R) := hs.trans (ball_subset_ball (by linarith))
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  let Z := weak_variation_on_ball X isOpen_ball x (show 0 ≤ 6 * R by positivity)
    h68 V hV CV hCV φ hc hφ6 t
  let Q := compose_on_ball Z isOpen_ball x (show 0 ≤ 4 * R by positivity)
    h46 B hB CB hCB
  let qt (z : LoopPlane) := ψ (variationValue X.value V φ t z)
  have hqt : (fun z => e (qt z)) =ᵐ[volume.restrict (ball x (4 * R))] Q.value := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    change e (ψ (variationValue X.value V φ t z)) = B (variationValue X.value V φ t z)
    exact hBψ _ (hcapture t ht (h48 hz))
  let G := lift_target Q e qt hqt
  have hmatch : ∀ᵐ z ∂volume.restrict (closedBall x (2 * R)),
      z ∉ closedBall x R → e (G.value z) = e (F.value z) ∧
        ∀ i, G.derivative i z = F.derivative i z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h28 hvalue,
      ae_all_iff.mpr (fun i => ae_restrict_of_ae_restrict_of_subset h28 (hfield i)),
      ae_restrict_mem measurableSet_closedBall] with z hv hd hz
    intro hn
    have hnφ : z ∉ tsupport φ := fun hm => hn (ball_subset_closedBall (hs hm))
    have hφ := image_eq_zero_of_notMem_tsupport hnφ
    have hDφ := fderiv_of_notMem_tsupport ℝ hnφ
    have hval : variationValue X.value V φ t z = X.value z := by
      simp only [variationValue, hφ, zero_smul, smul_zero, add_zero]
    have hder (i : Fin 2) : variationField X.value X.derivative V φ t i z = X.derivative i z := by
      simp only [variationField, hφ, hDφ, zero_apply, zero_smul, add_zero, smul_zero]
    change e (ψ (variationValue X.value V φ t z)) = e (F.value z) ∧
      ∀ i, fderiv ℝ B (variationValue X.value V φ t z)
        (variationField X.value X.derivative V φ t i z) = F.derivative i z
    rw [hBψ _ (hcapture t ht (h28 hz)), hval]
    exact ⟨hv, fun i => by rw [hder i]; exact hd i⟩
  obtain ⟨H, hin, hout⟩ := exists_supported_replacement F G x hR.le (by linarith)
    hDU h24 hmatch
  exact ⟨H, hin, hout⟩

end PoincareConjecture.M65Euler
