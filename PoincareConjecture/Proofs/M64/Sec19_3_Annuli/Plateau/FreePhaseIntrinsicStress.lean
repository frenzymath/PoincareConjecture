import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusStressIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhasePeriodicStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakModulusBalance













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem M64ObservedWeakAnnulus.intrinsic_stress_integral_eq_zero
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) {r : ℝ} (hr : 0 < r)
    (hminimum : ∀ s : ℝ, 0 < s → A.weightedEnergy Q r ≤ A.weightedEnergy Q s) :
    (∫ p in S, r * m60AreaGram g A.map p 0 0 -
      r⁻¹ * m60AreaGram g A.map p 1 1) = 0 := by
  have heq : (∫ p in S, r * m60AreaGram g A.map p 0 0 -
      r⁻¹ * m60AreaGram g A.map p 1 1) =
      ∫ p in S, r * Q (A.map p) (A.column 0 p) (A.column 0 p) -
        r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p) := by
    apply integral_congr_ae
    filter_upwards [A.stress_eq_ae_of_contMDiffOn g he Q hdiag hA r] with p hp
    exact hp.1.symm
  rw [heq, integral_sub ((A.column_pair_integrable Q hQ hei hb 0 0).const_mul r)
    ((A.column_pair_integrable Q hQ hei hb 1 1).const_mul r⁻¹),
    integral_const_mul, integral_const_mul]
  exact sub_eq_zero.mpr (A.weightedEnergy_modulus_balance Q hQ hei hb hr hminimum)

namespace M64FreeWeakPhaseAnnulus

variable {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}




theorem intrinsic_periodic_source_stress_eq_zero
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hperiod0 : Function.Periodic c0 curvePeriod)
    (hperiod1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (hD : angularPoint (k * D) = angularPoint 0)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    (∫ p in S, deriv eta (p 0) * rho (p 1) *
      (r * m60AreaGram g A.annulus.map p 0 0 - r⁻¹ * m60AreaGram g A.annulus.map p 1 1) +
      eta (p 0) * deriv rho (p 1) * (2 * r⁻¹ * m60AreaGram g A.annulus.map p 0 1)) = 0 := by
  have h := A.periodic_source_stress_eq_zero hc0 hc1 hperiod0 hperiod1 hH0 hH1 hD
    Q hQ hei hb r hmin heta hperiod hrho hcompact
  calc
    _ = ∫ p in S, deriv eta (p 0) * rho (p 1) *
        (r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
          r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) +
        r⁻¹ * eta (p 0) * deriv rho (p 1) *
          (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
            Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p)) := by
      apply integral_congr_ae
      filter_upwards [A.annulus.stress_eq_ae_of_contMDiffOn g he Q hdiag hA r] with p hp
      rw [← hp.1, ← hp.2]
      ring
    _ = 0 := h

end M64FreeWeakPhaseAnnulus

end PoincareConjecture
