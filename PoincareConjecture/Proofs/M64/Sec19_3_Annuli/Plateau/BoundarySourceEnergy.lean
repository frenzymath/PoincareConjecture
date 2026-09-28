import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseSourcePullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 d0 d1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem M64ObservedWeakAnnulus.weightedEnergy_horizontalSource
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M64ObservedWeakAnnulus (n := n) e d0 d1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ)
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (hmap : B.map = A.map ∘ m64HorizontalSource tau)
    (hcolumn : ∀ i, ∀ᵐ p ∂mu, B.column i p =
      (if i = 0 then deriv tau (p 0) else 1) • A.column i (m64HorizontalSource tau p)) :
    B.weightedEnergy Q r =
      ∫ p in S,
        (r * deriv tau (tau.symm (p 0)) * Q (A.map p) (A.column 0 p) (A.column 0 p) +
          r⁻¹ * (deriv tau (tau.symm (p 0)))⁻¹ *
            Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
  let T := m64HorizontalSource tau
  let J := fun p : LoopPlane =>
    (r * deriv tau (tau.symm (p 0)) * Q (A.map p) (A.column 0 p) (A.column 0 p) +
      r⁻¹ * (deriv tau (tau.symm (p 0)))⁻¹ *
        Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  change B.weightedEnergy Q r = ∫ p in S, J p
  rw [← m64HorizontalSource_integral (ht.differentiable (by simp)) hpos hmono h0 hP J]
  unfold M64ObservedWeakAnnulus.weightedEnergy
  apply integral_congr_ae
  filter_upwards [hcolumn 0, hcolumn 1] with p hc0 hc1
  simp only [ite_true] at hc0
  simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false, one_smul] at hc1
  rw [hc0, hc1, hmap]
  simp only [Function.comp_apply, map_smul, smul_apply, smul_eq_mul]
  change (r * (deriv tau (p 0) *
      (deriv tau (p 0) * Q (A.map (T p)) (A.column 0 (T p)) (A.column 0 (T p)))) +
      r⁻¹ * Q (A.map (T p)) (A.column 1 (T p)) (A.column 1 (T p))) / 2 = _
  have hcoord : (T p) 0 = tau (p 0) := rfl
  dsimp only [J]
  rw [hcoord, Homeomorph.symm_apply_apply]
  field_simp [(hpos (p 0)).ne']
  ring

namespace M64FreeWeakPhaseAnnulus

variable {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

theorem horizontal_source_energy_minimum
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau) (h0 : tau 0 = 0)
    (hperiod : ∀ x, tau (x + curvePeriod) = tau x + curvePeriod) :
    A.annulus.weightedEnergy Q r ≤
      ∫ p in S,
        (r * deriv tau (tau.symm (p 0)) *
            Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
          r⁻¹ * (deriv tau (tau.symm (p 0)))⁻¹ *
            Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2 := by
  obtain ⟨B, hmap, hcol, -⟩ := A.exists_horizontalSource ht hi hpos hmono h0 hperiod
  have hP : tau curvePeriod = curvePeriod := by simpa only [zero_add, h0] using hperiod 0
  rw [← A.annulus.weightedEnergy_horizontalSource B.annulus Q r ht hpos hmono h0 hP
    hmap hcol]
  exact hmin B

end M64FreeWeakPhaseAnnulus
end PoincareConjecture
