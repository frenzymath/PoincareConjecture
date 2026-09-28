import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseGoodCircleReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseReplacementEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CircleConeComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain




theorem auxiliaryCircle_free_phase_circle_energy_comparison
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {R : E →L[ℝ] LoopPlane} (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) D)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hpos : ∀ q v, 0 ≤ B q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) D,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      closedBall a rho ⊆ S → ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        A.annulus.diskEnergy B a (rho * Real.exp (-s)) ≤
          C * A.annulus.angularEnergy a rho s := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let : TopologicalSpace.PseudoMetrizableSpace Q.charts.Point :=
    hei.isInducing.pseudoMetrizableSpace
  obtain ⟨epsilon, hepsilon, C0, hC0, hfill⟩ :=
    m64ChartReadable_uniform_H1_cone_energy g e he hei.isEmbedding hread B hB
  have hbounded : Bornology.IsBounded (range B) := (isCompact_range hB).isBounded
  obtain ⟨K, hK⟩ := hbounded.exists_norm_le
  have hbound (q : Q.charts.Point) : ‖B q‖ ≤ K := hK _ (mem_range_self q)
  let T := (max modulus modulus⁻¹) ^ 2
  have hT : 0 ≤ T := sq_nonneg _
  have hE := A.annulus.energy_nonneg B hpos
  let C := T * C0 + A.annulus.energy B / epsilon + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCC : T * C0 ≤ C := by dsimp only [C]; linarith [div_nonneg hE hepsilon.le]
  have hEC : A.annulus.energy B / epsilon ≤ C := by
    dsimp only [C]
    linarith [mul_nonneg hT hC0]
  refine ⟨C, hC, ?_⟩
  intro a rho hrho hKS
  have hcircles := A.annulus.local_circle_traces hei a hrho hKS
  have hreplace := auxiliaryCircle_free_phase_circle_replacements P Q he.continuous hR
    A a hrho hKS
  filter_upwards [hcircles, hreplace, ae_restrict_mem measurableSet_Icc]
    with s hcircle hreplacement hs
  let r := rho * Real.exp (-s)
  let v := fun x => m64MorreyPolarAngularColumn a rho (fun i p => A.annulus.column i p)
    (annulusPoint x s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hrrho : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
  have hball : ball a r ⊆ S :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hrrho).trans hKS)
  have hang : 0 ≤ A.annulus.angularEnergy a rho s := A.annulus.angularEnergy_nonneg a rho s
  by_cases hsmall : A.annulus.angularEnergy a rho s < epsilon
  · obtain ⟨gamma, w, hgc, hgp, hga, hv, -, -, hw, hwp, huni, hder⟩ := hcircle
    have hvp : Function.Periodic v curvePeriod :=
      m64MorreyPolarAngularColumn_periodic a rho (fun i p => A.annulus.column i p) s
    have hUp : Function.Periodic (e ∘ gamma) curvePeriod := fun x => congrArg e (hgp x)
    obtain ⟨hva, hunia, hdera, hFTCa, hEshift⟩ :=
      m64Periodic_H1_shift w hw hwp (e ∘ gamma) v hUp hvp hv huni hder Real.pi
    have hwa (j : ℕ) : ContDiff ℝ 1 (fun x => w j (x + Real.pi)) :=
      (hw j).comp (contDiff_id.add contDiff_const)
    have hshiftSmall : (∫ x in Icc (0 : ℝ) curvePeriod, ‖v (x + Real.pi)‖ ^ 2) < epsilon := by
      rw [hEshift]
      exact hsmall
    obtain ⟨cone, hconeE⟩ := hfill (fun x => gamma (x + Real.pi))
      (hgc.comp (continuous_id.add continuous_const)) (hgp.add_const Real.pi)
      (fun j x => w j (x + Real.pi)) hwa (fun j => (hwp j).add_const Real.pi)
      hunia (fun x => v (x + Real.pi)) hva
      (by simpa +instances only [Function.comp_def, zero_add] using! hFTCa) hdera hshiftSmall
    obtain ⟨W, hW0, hW1, hWm, hWc⟩ := hreplacement gamma hgc hgp hga cone
    have hlocal := A.weighted_local_energy_le_of_replacement W hW0 hW1
      B hB hei.isEmbedding hbound hpos hmodulus (hminimum W) measurableSet_ball hball
      (cone.affineMap a r) (hei.isEmbedding.aestronglyMeasurable_comp_iff.mp
        (cone.affine_memLp a hr).aestronglyMeasurable)
      (cone.affineColumn a r) (cone.affine_column_memLp a hr) hWm hWc
    rw [cone.affine_energy a hr B] at hlocal
    have hconeE' : cone.energy B ≤ C0 * A.annulus.angularEnergy a rho s := by
      simpa +instances only [hEshift, M64ObservedWeakAnnulus.angularEnergy, v] using! hconeE
    calc
      _ ≤ T * cone.energy B := hlocal
      _ ≤ T * (C0 * A.annulus.angularEnergy a rho s) := mul_le_mul_of_nonneg_left hconeE' hT
      _ = (T * C0) * A.annulus.angularEnergy a rho s := by ring
      _ ≤ C * A.annulus.angularEnergy a rho s := mul_le_mul_of_nonneg_right hCC hang
  · have hlarge : epsilon ≤ A.annulus.angularEnergy a rho s := le_of_not_gt hsmall
    calc
      _ ≤ A.annulus.energy B :=
        A.annulus.diskEnergy_le_energy B hB hei.isEmbedding hbound hpos a r hball
      _ = (A.annulus.energy B / epsilon) * epsilon := (div_mul_cancel₀ _ hepsilon.ne').symm
      _ ≤ (A.annulus.energy B / epsilon) * A.annulus.angularEnergy a rho s :=
        mul_le_mul_of_nonneg_left hlarge (div_nonneg hE hepsilon.le)
      _ ≤ C * A.annulus.angularEnergy a rho s := mul_le_mul_of_nonneg_right hEC hang

end PoincareConjecture.M64
