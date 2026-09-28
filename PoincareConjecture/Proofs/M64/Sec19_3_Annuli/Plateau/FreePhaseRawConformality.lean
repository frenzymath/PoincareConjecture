import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseStressZero
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSmoothGram













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





theorem auxiliaryCircle_free_phase_raw_conformal
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
    (hA : ContinuousOn A.annulus.map S) :
    ∀ p ∈ S,
      r * m60AreaGram g A.annulus.map p 0 0 =
        r⁻¹ * m60AreaGram g A.annulus.map p 1 1 ∧
      m60AreaGram g A.annulus.map p 0 1 = 0 := by
  have hsm := auxiliaryCircle_free_phase_contMDiffOn P Q e he hei.isEmbedding hread R hR A
    g B hB hb hdiag hr (hminimum r hr) hA
  have hz := auxiliaryCircle_free_phase_stress_eq_zero P Q e he hei hread R hR A
    hc0 hc1 hperiod0 hperiod1 hH0 hH1 hdegree g B hB hb hpos hdiag hr hminimum
  have heq := A.annulus.stress_eq_ae_of_contMDiffOn g he B hdiag
    (hsm.of_le (by simp)) r
  have hc : ∀ᵐ p ∂mu,
      r * m60AreaGram g A.annulus.map p 0 0 =
        r⁻¹ * m60AreaGram g A.annulus.map p 1 1 ∧
      m60AreaGram g A.annulus.map p 0 1 = 0 := by
    filter_upwards [heq, hz.1, hz.2] with p hp hU hV
    refine ⟨sub_eq_zero.mp (hp.1.symm.trans hU), ?_⟩
    exact (mul_eq_zero.mp (hp.2.symm.trans hV)).resolve_left
      (mul_ne_zero (by norm_num) (inv_ne_zero hr.ne'))
  have hcont (i j : Fin 2) : ContinuousOn (fun p => m60AreaGram g A.annulus.map p i j) S :=
    fun p hp => (m64AreaGram_entry_contDiffAt
      (hsm.contMDiffAt (isOpen_interior.mem_nhds hp)) i j).continuousAt.continuousWithinAt
  have hdiagPt := Measure.eqOn_open_of_ae_eq (hc.mono fun _ h => h.1) isOpen_interior
    (continuousOn_const.mul (hcont 0 0)) (continuousOn_const.mul (hcont 1 1))
  have hcrossPt := Measure.eqOn_open_of_ae_eq (hc.mono fun _ h => h.2) isOpen_interior
    (hcont 0 1) continuousOn_const
  exact fun p hp => ⟨hdiagPt hp, hcrossPt hp⟩

end PoincareConjecture.M64
