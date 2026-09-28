import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseHalfTurnMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseLocalizedStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressTwoCuts













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "a" => curvePeriod / 2
local notation "T" => m64AnnulusHalfTurn




theorem periodic_source_stress_eq_zero
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hperiod0 : Function.Periodic c0 curvePeriod)
    (hperiod1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (hD : angularPoint (k * D) = angularPoint 0)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    (∫ p in S, deriv eta (p 0) * rho (p 1) *
      (r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) +
      r⁻¹ * eta (p 0) * deriv rho (p 1) *
        (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
          Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))) = 0 := by
  let U := fun (B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
      (p : LoopPlane) =>
    r * Q (B.annulus.map p) (B.annulus.column 0 p) (B.annulus.column 0 p) -
      r⁻¹ * Q (B.annulus.map p) (B.annulus.column 1 p) (B.annulus.column 1 p)
  let V := fun (B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
      (p : LoopPlane) => r⁻¹ *
    (Q (B.annulus.map p) (B.annulus.column 0 p) (B.annulus.column 1 p) +
      Q (B.annulus.map p) (B.annulus.column 1 p) (B.annulus.column 0 p))
  have hi (i j : Fin 2) : Integrable (fun p =>
      Q (A.annulus.map p) (A.annulus.column i p) (A.annulus.column j p)) mu :=
    A.annulus.column_pair_integrable Q hQ hei hb i j
  have hU : Integrable (U A) mu := ((hi 0 0).const_mul r).sub ((hi 1 1).const_mul r⁻¹)
  have hV : Integrable (V A) mu := ((hi 0 1).add (hi 1 0)).const_mul r⁻¹
  have hbase (B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
      (hB : ∀ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
        B.annulus.weightedEnergy Q r ≤ C.annulus.weightedEnergy Q r)
      (xi : ℝ → ℝ) (hxi : ContDiff ℝ ∞ xi)
      (hxp : Function.Periodic xi curvePeriod) (hx0 : xi 0 = 0) :
      (∫ p in S, deriv xi (p 0) * rho (p 1) * U B p +
        xi (p 0) * deriv rho (p 1) * V B p) = 0 := by
    have h := B.localized_source_stress_eq_zero hc0 hc1 hH0 hH1 Q hQ hei hb r hB
      hxi hxp hx0 hrho hcompact
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with p
    dsimp only [U, V]
    ring
  have hfull : (∫ p in S, deriv eta (p 0) * rho (p 1) * U A p +
      eta (p 0) * deriv rho (p 1) * V A p) = 0 := by
    apply m64LocalizedStress_of_two_cuts hU hV hrho (hbase A hmin) ?_ heta hperiod
    intro xi hxi hxp hxa
    obtain ⟨B, hmap, hcol, -, hB⟩ := A.exists_halfTurn_minimum
      hc0 hc1 hperiod0 hperiod1 hH0 hH1 hD Q hQ hei hb r hmin
    let theta : ℝ → ℝ := fun x => xi (x + a)
    have ht : ContDiff ℝ ∞ theta := hxi.comp (contDiff_id.add contDiff_const)
    have htp : Function.Periodic theta curvePeriod := by
      intro x
      dsimp only [theta]
      rw [show x + curvePeriod + a = (x + a) + curvePeriod by ring, hxp]
    have ht0 : theta 0 = 0 := by simpa only [theta, zero_add] using hxa
    have h := hbase B hB theta ht htp ht0
    have heq : (∫ p in S, deriv theta (p 0) * rho (p 1) * U B p +
        theta (p 0) * deriv rho (p 1) * V B p) =
        ∫ p in S, deriv theta (p 0) * rho (p 1) * U A (T p) +
          theta (p 0) * deriv rho (p 1) * V A (T p) := by
      apply integral_congr_ae
      filter_upwards [hcol 0, hcol 1] with p h0 h1
      dsimp only [U, V]
      rw [hmap, h0, h1]
      rfl
    rw [heq, m64LocalizedStress_halfTurn hU hV hxi hxp hrho] at h
    exact h
  convert hfull using 1
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp only [U, V]
  ring

end PoincareConjecture.M64FreeWeakPhaseAnnulus
