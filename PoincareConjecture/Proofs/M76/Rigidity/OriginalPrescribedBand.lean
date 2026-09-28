import PoincareConjecture.Proofs.M76.Rigidity.OriginalBandWidth
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBandOpenness









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}




theorem OriginalDiskProduct.exists_open_prescribed_band_lift
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (hopenP : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (F : E → X) (hF : PolyhedralPLInCharts e F (Q ×ˢ I))
    (hFi : InjOn F (Q ×ˢ I)) (hfront : MapsTo F (Q ×ˢ I) (frontier R))
    (hcenter : ∀ z ∈ Q, F (z, 0) = j z)
    (hopenF : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (F '' (Q ×ˢ Ioo (-1 : ℝ) 1)))) :
    ∃ (a : ℝ) (q : E → E), 0 < a ∧ a ≤ 1 / 2 ∧
      FinitePiecewiseAffineOn q (Q ×ˢ Icc (-a) a) ∧
      InjOn q (Q ×ˢ Icc (-a) a) ∧
      MapsTo q (Q ×ˢ Icc (-a) a) (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ z ∈ Q, q (z, 0) = (z, 0)) ∧
      (∀ z ∈ Q ×ˢ Icc (-a) a, (q z).2 = 0 ↔ z.2 = 0) ∧
      (∀ z ∈ Q ×ˢ Icc (-a) a, P.map (q z) = F z) ∧
      IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
        (q '' (Q ×ˢ Ioo (-a) a))) := by
  obtain ⟨a, ha, hasmall, hband⟩ := P.exists_prescribed_band_width
    he.closed hopenP F hF.continuousOn hfront hcenter
  have ha1 : a ≤ 1 := by linarith
  obtain ⟨k, _, hleft, hback, _, hq, hqi, hqm, hqc, hqzero⟩ :=
    P.exists_prescribed_band_coordinates he F hF hFi hfront hcenter ha ha1 hband
  have hhalf : D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ D ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hbackF (z : E) (hz : z ∈ Q ×ˢ Icc (-a) a) :
      P.map (k (F z)) = F z := hback (F z) (image_mono hhalf (hband hz))
  have hopenSmall := Set.InjOn.isOpen_smaller_band_image (isCompact_sphere (0 : V2) 1)
    hFi hF.continuousOn hopenF ha1
  exact ⟨a, k ∘ F, ha, hasmall, hq, hqi, hqm, hqc, hqzero, hbackF,
    P.isOpen_prescribed_band_coordinates F k hleft hbackF hqm hopenSmall⟩

end PoincareConjecture.M76
