import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreePhaseDegreeEnergy









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

namespace M64ObservedWeakAnnulus



theorem constant_reader_vertical_integral
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (T : E →L[ℝ] ℝ) {v0 v1 : ℝ}
    (h0 : ∀ x, T (e (c0 x)) = v0) (h1 : ∀ x, T (e (c1 x)) = v1) :
    (∫ p in S, T (A.column 1 p)) = curvePeriod * (v1 - v0) := by
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top⟩
  have hi : Integrable (A.column 1) mu := (Lp.memLp (A.column 1)).integrable (by norm_num)
  have hb : IntegrableOn (fun x => e (c1 x) - e (c0 x))
      (Icc (0 : ℝ) curvePeriod) volume := (hc1.sub hc0).integrableOn_Icc
  have hg := A.boundary (fun _ => 1) contDiff_const
  simp only [fderiv_const_apply, zero_apply, zero_smul, integral_zero, add_zero,
    one_smul] at hg
  have hh := congrArg T hg
  rw [← T.integral_comp_comm hi, ← T.integral_comp_comm hb] at hh
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  simpa [Function.comp_def, h0, h1, hP] using hh



theorem weightedEnergy_ge_constant_reader
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (T : E →L[ℝ] ℝ) {v0 v1 : ℝ}
    (h0 : ∀ x, T (e (c0 x)) = v0) (h1 : ∀ x, T (e (c1 x)) = v1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {r : ℝ} (hr : 0 < r) :
    r⁻¹ * curvePeriod * (v1 - v0) ^ 2 / (2 * max (‖T‖ ^ 2 * C) 1) ≤
      A.weightedEnergy B r := by
  let C' := max (‖T‖ ^ 2 * C) 1
  have hC' : 0 < C' := lt_max_of_lt_right zero_lt_one
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hTcol : MemLp (fun p => T (A.column 1 p)) 2 mu :=
    T.comp_memLp' (Lp.memLp (A.column 1))
  have hp := m64Annulus_integral_sq_le hTcol
  rw [A.constant_reader_vertical_integral hc0 hc1 T h0 h1] at hp
  have hboundary : curvePeriod * (v1 - v0) ^ 2 ≤
      ∫ p in S, T (A.column 1 p) ^ 2 := by
    by_contra h
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge h) hP
    nlinarith [hp]
  have hi : Integrable (fun p => ‖A.column 1 p‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A.column 1))).mp
      (Lp.memLp (A.column 1))
  have hreader : (∫ p in S, T (A.column 1 p) ^ 2) ≤ ‖T‖ ^ 2 * ‖A.column 1‖ ^ 2 := by
    rw [LpFiniteCoordinatesNative.l2_norm_sq, ← integral_const_mul]
    apply integral_mono_ae hTcol.integrable_sq (hi.const_mul _)
    filter_upwards with p
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
      (norm_nonneg (A.column 1 p)))).mpr (T.le_opNorm (A.column 1 p))
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hh
  have hI1 : 0 ≤ ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p) :=
    integral_nonneg fun p => hpos _ _
  have henergy : curvePeriod * (v1 - v0) ^ 2 ≤ C' *
      ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p) := by
    calc
      _ ≤ ‖T‖ ^ 2 * ‖A.column 1‖ ^ 2 := hboundary.trans hreader
      _ ≤ ‖T‖ ^ 2 * (C * ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p)) :=
        mul_le_mul_of_nonneg_left
          (A.column_norm_sq_le_column_energy B hB hei hb hcoercive 1) (sq_nonneg _)
      _ = (‖T‖ ^ 2 * C) * ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hI1
  have hmain : r⁻¹ * curvePeriod * (v1 - v0) ^ 2 / (2 * C') ≤ (r⁻¹ / 2) *
      ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hC')).mpr
    calc
      _ = r⁻¹ * (curvePeriod * (v1 - v0) ^ 2) := by ring
      _ ≤ r⁻¹ * (C' * ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p)) :=
        mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr hr.le)
      _ = _ := by ring
  rw [A.weightedEnergy_eq_column_integrals B hB hei hb r]
  exact hmain.trans (le_add_of_nonneg_left
    (mul_nonneg (by positivity) (integral_nonneg fun p => hpos _ _)))

end M64ObservedWeakAnnulus



theorem M64FreeWeakPhaseAnnulus.weightedEnergy_ge_boundary_reader
    {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (T : E →L[ℝ] ℝ) {v0 v1 : ℝ}
    (h0 : ∀ x, T (e (c0 x)) = v0) (h1 : ∀ x, T (e (c1 x)) = v1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {r : ℝ} (hr : 0 < r) :
    r⁻¹ * curvePeriod * (v1 - v0) ^ 2 / (2 * max (‖T‖ ^ 2 * C) 1) ≤
      A.annulus.weightedEnergy B r := by
  obtain ⟨hlabel0, hlabel1⟩ := A.labels_continuous hH0 hH1
  exact A.annulus.weightedEnergy_ge_constant_reader (hc0.comp hlabel0) (hc1.comp hlabel1)
    T (fun x => h0 (A.label0 x)) (fun x => h1 (A.label1 x)) B hB hei hb hpos hcoercive hr

end PoincareConjecture
