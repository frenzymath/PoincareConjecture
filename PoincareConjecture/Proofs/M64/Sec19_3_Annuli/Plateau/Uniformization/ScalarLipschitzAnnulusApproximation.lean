import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAnnulusDescentArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarIntrinsicChartLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarRelativeAreaApproximation













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem scalarAnnulus_exists_C1_physical_approximation
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Plane → M, ContMDiffOn (𝓡 2) (𝓡 n) 1 G {p | p ≠ 0} ∧
      (∀ x : ℝ, G (scalarCoverMap (1, x / curvePeriod)) = c0 x) ∧
      (∀ x : ℝ, G (scalarCoverMap (2, x / curvePeriod)) = c1 x) ∧
      IntegrableOn (m60AreaDensity g G) scalarAnnulus ∧
      (∫ p in scalarAnnulus, m60AreaDensity g G p) < A.area + eps := by
  obtain ⟨B, hBA, hBlo, hBhi, -⟩ := scalarAnnulus_exists_flat_collars A hc0 hc1
  obtain ⟨F, hFc, hdesc, hFL⟩ := scalarAnnulus_exists_physical_descent B
  obtain ⟨hFI, hFA⟩ := scalarAnnulusDescent_area B hdesc
  have hlocal := scalar_locallyChartLipschitz_of_intrinsic g hFL
  let K : Set Plane := {p | ‖p‖ ∈ Icc (5 / 4 : ℝ) (3 / 2)}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : Plane) (3 / 2)).of_isClosed_subset
      (isClosed_Icc.preimage continuous_norm)
    intro p hp
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2
  have hKW : K ⊆ scalarAnnulus := by
    intro p hp
    change 1 < ‖p‖ ∧ ‖p‖ < 2
    have hp' : 5 / 4 ≤ ‖p‖ ∧ ‖p‖ ≤ (3 / 2 : ℝ) := hp
    constructor <;> linarith
  have hWO : scalarAnnulus ⊆ {p : Plane | p ≠ 0} := by
    intro p hp
    exact norm_pos_iff.mp (zero_lt_one.trans hp.1)
  have hO : IsOpen {p : Plane | p ≠ 0} := isOpen_ne
  obtain ⟨G, -, -, hGa, hGp, hGK, -, hGI, hGA⟩ :=
    scalar_exists_relative_area_approximation g F hO scalarAnnulus_isOpen hWO subset_rfl
      hK hKW scalarAnnulus_isOpen.measurableSet hFc hlocal hFI heps
  have hGC1 : ContMDiffOn (𝓡 2) (𝓡 n) 1 G {p | p ≠ 0} := by
    intro p hp
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hpK : p ∈ K
    · exact hGK p hpK
    · apply hGp p
      apply scalarAnnulusDescent_contMDiffAt_of_flat_collars hc0 hc1 hBlo hBhi hdesc hp
      by_cases hlo : ‖p‖ < (5 / 4 : ℝ)
      · exact Or.inl hlo
      · exact Or.inr (lt_of_not_ge (fun hhi => hpK ⟨le_of_not_gt hlo, hhi⟩))
  have hboundary (r : ℝ) (hr : r = 1 ∨ r = 2) (x : ℝ) :
      G (scalarCoverMap (r, x / curvePeriod)) = F (scalarCoverMap (r, x / curvePeriod)) := by
    apply (hGa _ _).self_of_nhds
    have hnorm : ‖scalarCoverMap (r, x / curvePeriod)‖ = r := by
      rw [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos]
      rcases hr with rfl | rfl <;> norm_num
    intro hp
    change 1 < ‖scalarCoverMap (r, x / curvePeriod)‖ ∧
      ‖scalarCoverMap (r, x / curvePeriod)‖ < 2 at hp
    rw [hnorm] at hp
    rcases hr with rfl | rfl <;> linarith [hp.1, hp.2]
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  refine ⟨G, hGC1, ?_, ?_, hGI, ?_⟩
  · intro x
    rw [hboundary 1 (Or.inl rfl), hdesc _ (by norm_num)]
    simpa only [scalarAnnulusCoverLift, scalarAnnulusClamp, sub_self,
      projIcc_left, mul_div_cancel₀ x hP] using B.lower_boundary x
  · intro x
    rw [hboundary 2 (Or.inr rfl), hdesc _ (by norm_num)]
    simpa only [scalarAnnulusCoverLift, scalarAnnulusClamp, show (2 : ℝ) - 1 = 1 by norm_num,
      projIcc_right, mul_div_cancel₀ x hP] using B.upper_boundary x
  · rw [hFA, hBA] at hGA
    exact hGA

end PoincareConjecture.M64Uniformization
