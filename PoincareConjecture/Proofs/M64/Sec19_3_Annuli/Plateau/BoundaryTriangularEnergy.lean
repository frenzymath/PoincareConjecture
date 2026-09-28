import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseTriangularSource







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture



def m64TriangularEnergyDensity (r a b q00 q01 q10 q11 : ℝ) : ℝ :=
  (r * a * q00 + r⁻¹ * a⁻¹ * (b ^ 2 * q00 + b * q01 + b * q10 + q11)) / 2

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 d0 d1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)



theorem M64ObservedWeakAnnulus.weightedEnergy_triangularSource
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M64ObservedWeakAnnulus (n := n) e d0 d1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ)
    (T : LoopPlane ≃ₜ LoopPlane) (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S) (hmap : B.map = A.map ∘ T)
    (hcolumn : ∀ i, ∀ᵐ p ∂mu, B.column i p =
      if i = 0 then fderiv ℝ T p e0 0 • A.column 0 (T p)
      else fderiv ℝ T p e1 0 • A.column 0 (T p) + A.column 1 (T p)) :
    B.weightedEnergy Q r = ∫ p in S, m64TriangularEnergyDensity r
      (fderiv ℝ T (T.symm p) e0 0) (fderiv ℝ T (T.symm p) e1 0)
      (Q (A.map p) (A.column 0 p) (A.column 0 p))
      (Q (A.map p) (A.column 0 p) (A.column 1 p))
      (Q (A.map p) (A.column 1 p) (A.column 0 p))
      (Q (A.map p) (A.column 1 p) (A.column 1 p)) := by
  let J := fun p : LoopPlane => m64TriangularEnergyDensity r
    (fderiv ℝ T (T.symm p) e0 0) (fderiv ℝ T (T.symm p) e1 0)
    (Q (A.map p) (A.column 0 p) (A.column 0 p))
    (Q (A.map p) (A.column 0 p) (A.column 1 p))
    (Q (A.map p) (A.column 1 p) (A.column 0 p))
    (Q (A.map p) (A.column 1 p) (A.column 1 p))
  change B.weightedEnergy Q r = ∫ p in S, J p
  rw [← m64TriangularSource_integral T hT hsecond hpos hpre J]
  unfold M64ObservedWeakAnnulus.weightedEnergy
  apply integral_congr_ae
  filter_upwards [hcolumn 0, hcolumn 1] with p hc0 hc1
  simp only [ite_true] at hc0
  simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false] at hc1
  rw [hc0, hc1, hmap]
  simp only [J, m64TriangularEnergyDensity, Homeomorph.symm_apply_apply,
    Function.comp_apply, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  field_simp [(hpos p).ne']
  ring

namespace M64FreeWeakPhaseAnnulus

variable {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}




theorem triangular_source_energy_minimum
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s)
    (hshift : ∀ x s, T (annulusPoint (x + curvePeriod) s) =
      T (annulusPoint x s) + annulusPoint curvePeriod 0) :
    A.annulus.weightedEnergy Q r ≤ ∫ p in S, m64TriangularEnergyDensity r
      (fderiv ℝ T (T.symm p) e0 0) (fderiv ℝ T (T.symm p) e1 0)
      (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p))
      (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p))
      (Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
      (Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) := by
  obtain ⟨B, hmap, hcolumn, -⟩ := A.exists_triangularSource hc0 hc1 hH0 hH1
    T hT hi hsecond hpos hpre hzero hperiod hshift
  rw [← A.annulus.weightedEnergy_triangularSource B.annulus Q r T
    (hT.differentiable (by simp)) hsecond hpos hpre hmap hcolumn]
  exact hmin B

end M64FreeWeakPhaseAnnulus
end PoincareConjecture
