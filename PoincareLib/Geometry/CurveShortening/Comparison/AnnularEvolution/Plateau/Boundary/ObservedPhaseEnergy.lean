import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.PhaseCircleColumns
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.RegularityCharts
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Variable.ModulusEnergy

/-!
# Phase energy from the actual observed weak annulus

The retained linear circle reader and the genuine real H1 quotient
identity determine the phase columns. Their energy is therefore bounded
by the observed annular energy without a separate phase-energy premise.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareMT.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

/-- The actual observed circle reader identifies the squared norm of each original phase
column exactly. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary
constructions in `proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`,
Mathematical Checks. -/
theorem real_phase_column_norm_sq
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (R : E →L[ℝ] LoopPlane) (k : ℝ)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u S)
    (hphase : (fun p => R (e (A.map p))) =ᵐ[mu] fun p => angularPoint (k * u p)) :
    ∀ i, ∀ᵐ p ∂mu, ‖R (A.column i p)‖ ^ 2 = k ^ 2 * (V i p) ^ 2 :=
  m64WeakPhase_circle_column_norm_sq isOpen_interior hu hV hw
    (fun p => R (e (A.map p))) (fun i p => R (A.column i p))
    (fun i => R.comp_memLp' (Lp.memLp (A.column i)))
    (fun i j => m64WeakPartial_comp_linear A.observed_memLp (Lp.memLp (A.column i))
      (A.weak_partial i) R j) k hphase

/-- A nonzero phase scale bounds each actual phase-column energy by the observed L2 column
norm. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary constructions
in `proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Mathematical
Checks. -/
theorem real_phase_column_integral_le_norm_sq
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (R : E →L[ℝ] LoopPlane) {k : ℝ} (hk : k ≠ 0)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u S)
    (hphase : (fun p => R (e (A.map p))) =ᵐ[mu] fun p => angularPoint (k * u p)) (i : Fin 2) :
    (∫ p in S, (V i p) ^ 2) ≤ (‖R‖ ^ 2 / k ^ 2) * ‖A.column i‖ ^ 2 := by
  have hsq : 0 < k ^ 2 := sq_pos_of_ne_zero hk
  have hid := A.real_phase_column_norm_sq R k hu hV hw hphase i
  have hi : Integrable (fun p => ‖A.column i p‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A.column i))).mp
      (Lp.memLp (A.column i))
  calc
    _ ≤ ∫ p in S, (‖R‖ ^ 2 / k ^ 2) * ‖A.column i p‖ ^ 2 := by
      apply integral_mono_ae (hV i).integrable_sq (hi.const_mul _)
      filter_upwards [hid] with p hp
      have hop := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg R)
        (norm_nonneg (A.column i p)))).mpr (R.le_opNorm (A.column i p))
      rw [hp, mul_pow] at hop
      rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
      nlinarith
    _ = _ := by rw [integral_const_mul, ← LpFiniteCoordinatesNative.l2_norm_sq]

/-- The actual observed coercivity and positive modulus interval bound the original phase
energy by the weighted annular energy. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Mathematical
Checks. -/
theorem real_phase_column_integral_le_weightedEnergy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (R : E →L[ℝ] LoopPlane) {k : ℝ} (hk : k ≠ 0)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u S)
    (hphase : (fun p => R (e (A.map p))) =ᵐ[mu] fun p => angularPoint (k * u p))
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {lo hi r : ℝ} (hlo : 0 < lo) (hr : r ∈ Icc lo hi) (i : Fin 2) :
    (∫ p in S, (V i p) ^ 2) ≤
      ((‖R‖ ^ 2 / k ^ 2) * (2 * C) * max lo⁻¹ hi) * A.weightedEnergy B r := by
  have hf : 0 ≤ ‖R‖ ^ 2 / k ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ (‖R‖ ^ 2 / k ^ 2) * ‖A.column i‖ ^ 2 :=
      A.real_phase_column_integral_le_norm_sq R hk hu hV hw hphase i
    _ ≤ (‖R‖ ^ 2 / k ^ 2) * (2 * C * A.energy B) :=
      mul_le_mul_of_nonneg_left
        (A.column_norm_sq_le_energy B hB hei hb hpos hC hcoercive i) hf
    _ ≤ (‖R‖ ^ 2 / k ^ 2) * (2 * C * (max lo⁻¹ hi * A.weightedEnergy B r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (A.energy_le_weightedEnergy_of_mem B hB hei hb hpos hlo hr)
        (mul_nonneg (by norm_num) hC)) hf
    _ = _ := by ring

end PoincareMT.M64ObservedWeakAnnulus
