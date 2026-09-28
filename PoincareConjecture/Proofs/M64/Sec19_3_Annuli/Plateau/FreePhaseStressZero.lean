import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressZero
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhasePeriodicSecondStress
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhasePeriodicStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakModulusBalance

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem auxiliaryCircle_free_phase_stress_eq_zero
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hperiod0 : Function.Periodic c0 curvePeriod)
    (hperiod1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + degree)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + degree)
    (hdegree : angularPoint ((curvePeriod / circumference) * degree) = angularPoint 0)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {r : ℝ} (hr : 0 < r)
    (hminimum : ∀ s : ℝ, 0 < s →
      ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
        A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B s) :
    let U := fun p =>
      r * B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
    let V := fun p => r⁻¹ *
      (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
        B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
    U =ᵐ[mu] (fun _ => 0) ∧ V =ᵐ[mu] (fun _ => 0) := by
  let U := fun p =>
    r * B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
      r⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
  let V := fun p => r⁻¹ *
    (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
      B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
  have hi (i j : Fin 2) : Integrable (fun p =>
      B (A.annulus.map p) (A.annulus.column i p) (A.annulus.column j p)) mu :=
    A.annulus.column_pair_integrable B hB hei.isEmbedding hb i j
  have hUi : Integrable U mu := ((hi 0 0).const_mul r).sub ((hi 1 1).const_mul r⁻¹)
  have hVi : Integrable V mu := ((hi 0 1).add (hi 1 0)).const_mul r⁻¹
  apply m64AnnulusStress_eq_zero hUi hVi (sq_nonneg r)
  · intro eta rho heta hper hrho hcompact
    have h := A.periodic_source_stress_eq_zero hc0 hc1 hperiod0 hperiod1 hH0 hH1 hdegree
      B hB hei.isEmbedding hb r (hminimum r hr) heta hper hrho hcompact
    convert h using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp only [U, V]; ring
  · intro eta rho heta hper hrho _ hsupp
    exact auxiliaryCircle_free_phase_periodic_second_stress P Q e he hei hread R hR A
      hc0 hc1 hperiod0 hperiod1 hH0 hH1 hdegree g B hB hb hpos hdiag hr hminimum
      heta hper hrho hsupp
  · dsimp only [U]
    rw [integral_sub ((hi 0 0).const_mul r) ((hi 1 1).const_mul r⁻¹),
      integral_const_mul, integral_const_mul]
    exact sub_eq_zero.mpr (A.annulus.weightedEnergy_modulus_balance B hB hei.isEmbedding hb
      hr (fun s hs => hminimum s hs A))

end PoincareConjecture.M64
