import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseLocalizedStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff ENNReal Manifold intervalIntegral

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem localized_boundary_flux_primitive
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) (hzero : eta 0 = 0) :
    let U := fun p : LoopPlane =>
      r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
    let V := fun p : LoopPlane => r⁻¹ *
      (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
        Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
    ContinuousOn
      (fun s => ∫ y in (0 : ℝ)..s, m64HorizontalMoment (deriv eta) U y) (Icc (0 : ℝ) 1) ∧
      (∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        m64HorizontalMoment eta V s =
          ∫ y in (0 : ℝ)..s, m64HorizontalMoment (deriv eta) U y) ∧
      (∫ y in (0 : ℝ)..1, m64HorizontalMoment (deriv eta) U y) = 0 := by
  let U := fun p : LoopPlane =>
    r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
      r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
  let V := fun p : LoopPlane => r⁻¹ *
    (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
      Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
  have hi (i j : Fin 2) : Integrable (fun p =>
      Q (A.annulus.map p) (A.annulus.column i p) (A.annulus.column j p)) mu :=
    A.annulus.column_pair_integrable Q hQ hei hb i j
  have hU : Integrable U mu := by
    convert! ((hi 0 0).const_mul r).sub ((hi 1 1).const_mul r⁻¹) using 1
  have hV : Integrable V mu := by
    convert! ((hi 0 1).add (hi 1 0)).const_mul r⁻¹ using 1
  apply m64LocalizedStress_zero_boundary_moment hU hV heta
  intro rho hrho hcompact
  have hs := A.localized_source_stress_eq_zero hc0 hc1 hH0 hH1 Q hQ hei hb r hmin
    heta hperiod hzero hrho hcompact
  convert! hs using 1
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp only [U, V]
  ring

end PoincareConjecture.M64FreeWeakPhaseAnnulus
