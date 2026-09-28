import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseSecondStress
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseHalfTurnMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressTwoCuts

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "half" => curvePeriod / 2
local notation "T" => m64AnnulusHalfTurn

theorem auxiliaryCircle_free_phase_periodic_second_stress
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
        A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B s)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) (hrho : ContDiff ℝ ∞ rho)
    (hrhoS : tsupport rho ⊆ Ioo (0 : ℝ) 1) :
    let U := fun p =>
      r * B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
    let V := fun p => r⁻¹ *
      (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
        B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
    (∫ p in S, deriv eta (p 0) * rho (p 1) * (-(r ^ 2) * V p) +
      eta (p 0) * deriv rho (p 1) * U p) = 0 := by
  let U := fun (C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) degree) (p : LoopPlane) =>
    r * B (C.annulus.map p) (C.annulus.column 0 p) (C.annulus.column 0 p) -
      r⁻¹ * B (C.annulus.map p) (C.annulus.column 1 p) (C.annulus.column 1 p)
  let V := fun (C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) degree) (p : LoopPlane) => r⁻¹ *
    (B (C.annulus.map p) (C.annulus.column 0 p) (C.annulus.column 1 p) +
      B (C.annulus.map p) (C.annulus.column 1 p) (C.annulus.column 0 p))
  have hi (i j : Fin 2) : Integrable (fun p =>
      B (A.annulus.map p) (A.annulus.column i p) (A.annulus.column j p)) mu :=
    A.annulus.column_pair_integrable B hB hei.isEmbedding hb i j
  have hUi : Integrable (U A) mu := ((hi 0 0).const_mul r).sub ((hi 1 1).const_mul r⁻¹)
  have hVi : Integrable (fun p => -(r ^ 2) * V A p) mu :=
    (((hi 0 1).add (hi 1 0)).const_mul r⁻¹).const_mul (-(r ^ 2))
  have hbase (C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) degree)
      (hC : ∀ s : ℝ, 0 < s →
        ∀ Z : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
            e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
          C.annulus.weightedEnergy B r ≤ Z.annulus.weightedEnergy B s)
      (xi : ℝ → ℝ) (hxi : ContDiff ℝ ∞ xi)
      (hxp : Function.Periodic xi curvePeriod) (hx0 : xi 0 = 0) :
      (∫ p in S, deriv xi (p 0) * rho (p 1) * (-(r ^ 2) * V C p) +
        xi (p 0) * deriv rho (p 1) * U C p) = 0 := by
    obtain ⟨W, -, -, hW, hmap, hcol, -, -, -, hminimumW⟩ :=
      auxiliaryCircle_free_phase_continuous_minimum P Q he hei hread hR C g B hB hpos
        hdiag hr hC
    have hxP : xi curvePeriod = 0 := by simpa only [zero_add, hx0] using hxp 0
    have h := auxiliaryCircle_free_phase_second_stress_zero_cut P Q e he hei.isEmbedding
      hread R hR W g B hB hb hdiag hr (hminimumW r hr) hW hxi hrho hx0 hxP hrhoS
    change (∫ p in S, deriv xi (p 0) * rho (p 1) * (-(r ^ 2) * V W p) +
      xi (p 0) * deriv rho (p 1) * U W p) = 0 at h
    calc
      _ = ∫ p in S, deriv xi (p 0) * rho (p 1) * (-(r ^ 2) * V W p) +
          xi (p 0) * deriv rho (p 1) * U W p := by
        apply integral_congr_ae
        filter_upwards [hmap] with p hp
        dsimp only [U, V]
        rw [hp, hcol]
      _ = 0 := h
  apply m64LocalizedStress_of_two_cuts hVi hUi hrho (hbase A hminimum) ?_ heta hperiod
  intro xi hxi hxp hxhalf
  obtain ⟨C, hmap, hcol, henergy, -⟩ := A.exists_halfTurn_minimum
    hc0 hc1 hperiod0 hperiod1 hH0 hH1 hdegree B hB hei.isEmbedding hb r (hminimum r hr)
  have hC : ∀ s : ℝ, 0 < s →
      ∀ Z : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
        C.annulus.weightedEnergy B r ≤ Z.annulus.weightedEnergy B s :=
    fun s hs Z => (henergy r).trans_le (hminimum s hs Z)
  let theta : ℝ → ℝ := fun x => xi (x + half)
  have ht : ContDiff ℝ ∞ theta := hxi.comp (contDiff_id.add contDiff_const)
  have htp : Function.Periodic theta curvePeriod := by
    intro x
    dsimp only [theta]
    rw [show x + curvePeriod + half = (x + half) + curvePeriod by ring, hxp]
  have ht0 : theta 0 = 0 := by simpa only [theta, zero_add] using hxhalf
  have h := hbase C hC theta ht htp ht0
  have heq : (∫ p in S, deriv theta (p 0) * rho (p 1) * (-(r ^ 2) * V C p) +
      theta (p 0) * deriv rho (p 1) * U C p) =
      ∫ p in S, deriv theta (p 0) * rho (p 1) * (-(r ^ 2) * V A (T p)) +
        theta (p 0) * deriv rho (p 1) * U A (T p) := by
    apply integral_congr_ae
    filter_upwards [hcol 0, hcol 1] with p h0 h1
    dsimp only [U, V]
    rw [hmap, h0, h1]
    rfl
  rw [heq, m64LocalizedStress_halfTurn hVi hUi hxi hxp hrho] at h
  exact h

end PoincareConjecture.M64
