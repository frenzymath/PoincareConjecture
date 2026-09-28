import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundarySeparation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

theorem scalarInverseCylinderMap_potential {H : Plane → ℝ} {V : Cover → ℝ} {P : ℝ}
    (e : OpenPartialHomeomorph Cover Cover)
    (htarget : e.target = scalarPotentialStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    {p : Plane} (hp : p ∈ Strip) :
    H (scalarInverseCylinderMap e p) = p 1 := by
  have hy : scalarCylinderCoordinate p ∈ e.target := htarget ▸ hp
  have h := congrArg Prod.fst (e.right_inv hy)
  rw [he] at h
  exact h

theorem scalarInverseCylinderMap_boundary_approach
    {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)
    {H : Plane → ℝ} {V : Cover → ℝ} {P : ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Strip,
      ‖scalarInverseCylinderMap e p‖ - 1 ≤ C * p 1 ∧
        2 - ‖scalarInverseCylinderMap e p‖ ≤ C * (1 - p 1) := by
  obtain ⟨c, hc, hsep⟩ :=
    annular_harmonic_linear_boundary_separation D hHc hHs hlap hinner houter
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro p hp
  have hmem : scalarInverseCylinderMap e p ∈ scalarAnnulus :=
    scalarCoverMap_mem (hsource ▸ e.map_target (htarget ▸ hp))
  have h := hsep (scalarInverseCylinderMap e p)
    ((scalarAnnulusDefining_pos _).mpr hmem).le
  rw [scalarInverseCylinderMap_potential e htarget he hp] at h
  constructor
  · have h0 := mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hc.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h0
  · have h1 := mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr hc.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h1

theorem exists_smooth_modulus_cylinder_with_boundary_approach
    (g : RiemannianMetric 2 Plane) :
    ∃ (r C : ℝ), 0 < r ∧ 0 < C ∧ ∃ F : Plane → Plane,
      ContDiffOn ℝ ∞ F Strip ∧
      InjOn F scalarCylinderFundamental ∧
      F '' scalarCylinderFundamental = scalarAnnulus ∧
      (∀ x s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
        F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s)) ∧
      (∀ p ∈ Strip,
        r * m60AreaGram g F p 0 0 = r⁻¹ * m60AreaGram g F p 1 1 ∧
          m60AreaGram g F p 0 1 = 0) ∧
      ∀ p ∈ Strip,
        ‖F p‖ - 1 ≤ C * p 1 ∧ 2 - ‖F p‖ ≤ C * (1 - p 1) := by
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  obtain ⟨H, V, P, e, hHc, hHs, hlap, hinner, houter, hP, -, -, hdV,
    hsource, htarget, he, hes, hei, hdeck⟩ := exists_smooth_annular_cover_chart D
  obtain ⟨C, hC, hbound⟩ := scalarInverseCylinderMap_boundary_approach D
    hHc hHs hlap hinner houter e hsource htarget he
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  refine ⟨curvePeriod / P, C, div_pos hperiod hP, hC, scalarInverseCylinderMap e,
    scalarInverseCylinderMap_smooth e htarget hei,
    scalarInverseCylinderMap_injOn_fundamental e hsource htarget hdeck,
    scalarInverseCylinderMap_image_fundamental e hsource htarget hdeck, ?_, ?_, hbound⟩
  · intro x s hs
    change scalarInverseCoverMap e (scalarCylinderCoordinate (annulusPoint (x + curvePeriod) s)) = _
    rw [scalarCylinderCoordinate_periodic]
    exact scalarInverseCoverMap_periodic e hsource htarget hdeck (htarget ▸ hs)
  · intro p hp
    exact scalarInverseCylinderMap_modulus_conformal D hHs hdV hP e
      hsource htarget he hes hei hp

end PoincareConjecture.M64Uniformization
