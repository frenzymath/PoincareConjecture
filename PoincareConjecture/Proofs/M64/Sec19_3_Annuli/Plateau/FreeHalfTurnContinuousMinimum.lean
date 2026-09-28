import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseHalfTurnMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "T" => m64AnnulusHalfTurn

theorem auxiliaryCircle_free_phase_halfTurn_continuous_minimum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {R : E →L[ℝ] LoopPlane} (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + degree)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + degree)
    (hdegree : angularPoint ((curvePeriod / circumference) * degree) = angularPoint 0)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmod : 0 < modulus)
    (hminimum : ∀ s : ℝ, 0 < s →
      ∀ Z : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
        A.annulus.weightedEnergy B modulus ≤ Z.annulus.weightedEnergy B s) :
    ∃ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
      ContinuousOn W.annulus.map S ∧
      W.annulus.map =ᵐ[mu] A.annulus.map ∘ T ∧
      W.label0 = m64FreePhaseHalfTurnLabel A.label0 ∧
      W.label1 = m64FreePhaseHalfTurnLabel A.label1 ∧
      (∀ i, ∀ᵐ p ∂mu, W.annulus.column i p = A.annulus.column i (T p)) ∧
      (∀ s : ℝ, W.annulus.weightedEnergy B s = A.annulus.weightedEnergy B s) ∧
      ∀ s : ℝ, 0 < s →
        ∀ Z : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
            e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
          W.annulus.weightedEnergy B modulus ≤ Z.annulus.weightedEnergy B s := by
  obtain ⟨C, hmap, hcol, hlabel0, hlabel1⟩ :=
    A.exists_halfTurn hc0 hc1 hp0 hp1 hH0 hH1 hdegree
  have henergy := A.weightedEnergy_eq_of_halfTurn C hmap hcol B hB hei.isEmbedding hb
  have hminC : ∀ s : ℝ, 0 < s →
      ∀ Z : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
        C.annulus.weightedEnergy B modulus ≤ Z.annulus.weightedEnergy B s :=
    fun s hs Z => (henergy modulus).trans_le (hminimum s hs Z)
  obtain ⟨W, h0, h1, hW, hWae, hWcol, -, -, hWenergy, hminW⟩ :=
    auxiliaryCircle_free_phase_continuous_minimum P Q he hei hread hR C g B hB hpos
      hdiag hmod hminC
  refine ⟨W, hW, ?_, h0.trans hlabel0, h1.trans hlabel1, ?_, ?_, hminW⟩
  · simpa only [hmap] using hWae
  · intro i
    rw [hWcol]
    exact hcol i
  · intro s
    exact (hWenergy B s).trans (henergy s)

end PoincareConjecture.M64
