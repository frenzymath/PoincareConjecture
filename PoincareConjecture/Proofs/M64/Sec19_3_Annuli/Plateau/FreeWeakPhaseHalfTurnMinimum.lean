import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseHalfTurn
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy












set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold

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
local notation "T" => m64AnnulusHalfTurn




theorem weightedEnergy_eq_of_halfTurn
    (A B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hmap : B.annulus.map = A.annulus.map ∘ T)
    (hcol : ∀ i, ∀ᵐ p ∂mu, B.annulus.column i p = A.annulus.column i (T p))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ) :
    B.annulus.weightedEnergy Q r = A.annulus.weightedEnergy Q r := by
  unfold M64ObservedWeakAnnulus.weightedEnergy
  rw [← m64AnnulusHalfTurn_integral_comp
    (A.annulus.weightedEnergy_integrable Q hQ hei hb r).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hcol 0, hcol 1] with p h0 h1
  rw [hmap, h0, h1]
  rfl




theorem exists_halfTurn_minimum
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hperiod0 : Function.Periodic c0 curvePeriod)
    (hperiod1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (hD : angularPoint (k * D) = angularPoint 0)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ)
    (hmin : ∀ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ C.annulus.weightedEnergy Q r) :
    ∃ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      B.annulus.map = A.annulus.map ∘ T ∧
      (∀ i, ∀ᵐ p ∂mu, B.annulus.column i p = A.annulus.column i (T p)) ∧
      (∀ s : ℝ, B.annulus.weightedEnergy Q s = A.annulus.weightedEnergy Q s) ∧
      ∀ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
        B.annulus.weightedEnergy Q r ≤ C.annulus.weightedEnergy Q r := by
  obtain ⟨B, hmap, hcol, -, -⟩ :=
    A.exists_halfTurn hc0 hc1 hperiod0 hperiod1 hH0 hH1 hD
  have heq := A.weightedEnergy_eq_of_halfTurn B hmap hcol Q hQ hei hb
  exact ⟨B, hmap, hcol, heq, fun C => (heq r).trans_le (hmin C)⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
