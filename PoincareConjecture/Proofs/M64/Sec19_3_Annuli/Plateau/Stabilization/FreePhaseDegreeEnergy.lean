import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff Manifold ENNReal

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64Annulus_integral_sq_le {f : LoopPlane → ℝ} (hf : MemLp f 2 mu) :
    (∫ p in S, f p) ^ 2 ≤ curvePeriod * ∫ p in S, f p ^ 2 := by
  have hc : MemLp (fun _ : LoopPlane => (1 : ℝ)) 2 mu :=
    m64Annulus_continuous_memLp_two continuous_const
  have hvol : (∫ p in S, (1 : ℝ) ^ 2) = curvePeriod := by
    rw [m64AnnulusInteriorIntegral_eq_iterated_integrable _ hc.integrable_sq]
    have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
    simp [hP]
  simpa only [one_mul, hvol] using M64Uniformization.scalar_integral_mul_sq_le hc hf

theorem M64ObservedWeakAnnulus.column_norm_sq_le_column_energy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v) (i : Fin 2) :
    ‖A.column i‖ ^ 2 ≤ C * ∫ p in S, B (A.map p) (A.column i p) (A.column i p) := by
  rw [LpFiniteCoordinatesNative.l2_norm_sq]
  have hi : Integrable (fun p => ‖A.column i p‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A.column i))).mp
      (Lp.memLp (A.column i))
  rw [← integral_const_mul]
  apply integral_mono_ae hi ((A.column_energy_integrable B hB hei hb i).const_mul C)
  filter_upwards [A.tangent i] with p hp
  exact hcoercive (A.map p) (A.column i p) hp

namespace M64FreeWeakPhaseAnnulus

variable {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

theorem phase_horizontal_integral
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) :
    (∫ p in S, A.phaseColumn 0 p) = D := by
  have hh := A.phase_seam (fun _ => 1) contDiff_const (fun _ _ => rfl)
  simpa using hh

theorem phase_degree_energy
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) :
    D ^ 2 ≤ curvePeriod * ∫ p in S, (A.phaseColumn 0 p) ^ 2 := by
  simpa only [A.phase_horizontal_integral] using
    m64Annulus_integral_sq_le (Lp.memLp (A.phaseColumn 0))

theorem weightedEnergy_ge_degree
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hk : k ≠ 0)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {r : ℝ} (hr : 0 < r) :
    r * D ^ 2 / (2 * curvePeriod * max ((‖R‖ ^ 2 / k ^ 2) * C) 1) ≤
      A.annulus.weightedEnergy B r := by
  let C' := max ((‖R‖ ^ 2 / k ^ 2) * C) 1
  have hC' : 0 < C' := lt_max_of_lt_right zero_lt_one
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hf : 0 ≤ ‖R‖ ^ 2 / k ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hI0 : 0 ≤ ∫ p in S,
      B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) :=
    integral_nonneg fun p => hpos _ _
  have hp : (∫ p in S, (A.phaseColumn 0 p) ^ 2) ≤ C' *
      ∫ p in S, B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) := by
    calc
      _ ≤ (‖R‖ ^ 2 / k ^ 2) * ‖A.annulus.column 0‖ ^ 2 :=
        A.annulus.real_phase_column_integral_le_norm_sq R hk (Lp.memLp A.phase)
          (fun i => Lp.memLp (A.phaseColumn i)) A.phase_weak A.phase_observation 0
      _ ≤ (‖R‖ ^ 2 / k ^ 2) * (C * ∫ p in S,
          B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p)) :=
        mul_le_mul_of_nonneg_left
          (A.annulus.column_norm_sq_le_column_energy B hB hei hb hcoercive 0) hf
      _ = ((‖R‖ ^ 2 / k ^ 2) * C) * ∫ p in S,
          B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hI0
  have hd := A.phase_degree_energy.trans (mul_le_mul_of_nonneg_left hp hP.le)
  have hmain : r * D ^ 2 / (2 * curvePeriod * C') ≤ (r / 2) *
      ∫ p in S, B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) := by
    apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hP) hC')).mpr
    calc
      _ ≤ r * (curvePeriod * (C' * ∫ p in S,
          B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p))) :=
        mul_le_mul_of_nonneg_left hd hr.le
      _ = _ := by ring
  rw [A.annulus.weightedEnergy_eq_column_integrals B hB hei hb r]
  exact hmain.trans (le_add_of_nonneg_right
    (mul_nonneg (by positivity) (integral_nonneg fun p => hpos _ _)))

end M64FreeWeakPhaseAnnulus
end PoincareConjecture
