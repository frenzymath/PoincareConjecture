import PoincareConjecture.Proofs.M60.Mathlib.SUMovingQuadratic
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem suCompactMetric_coercive {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) (B : Y → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContinuousOn B K) (hpos : ∀ y ∈ K, ∀ v ≠ 0, 0 < B y v v) :
    ∃ a > 0, ∀ y ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤ B y v v := by
  have hc : ContinuousOn (fun q : Y × E => B q.1 q.2 q.2)
      (K ×ˢ Metric.sphere 0 1) :=
    ((hB.comp continuous_fst.continuousOn (fun _ h => h.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  obtain ⟨a, ha, hab⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_forall_le' hc
    (a := 0) (by
      intro q hq
      apply hpos q.1 hq.1 q.2
      intro hq0
      have := hq.2
      simp [hq0] at this)
  refine ⟨a, ha, ?_⟩
  intro y hy v
  by_cases hv : v = 0
  · simp [hv]
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : E) 1 := by
    simp [w, norm_smul, norm_inv, hnv]
  have hb := hab (y, w) ⟨hy, hw⟩
  have hscale : B y w w * ‖v‖ ^ 2 = B y v v := by
    dsimp only [w]
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  have := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  simpa only [hscale] using this

omit [FiniteDimensional ℝ E] in


theorem suCompactMetric_uniform_errors {X Y : Type*} [UniformSpace Y] [CompactSpace Y]
    (B : Y → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {u : ℕ → X → Y} {v : X → Y} (hu : TendstoUniformly u v atTop) :
    ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 0) ∧ (∀ n, 0 ≤ d n) ∧
      ∀ n x, ‖B (v x) - B (u n x)‖ ≤ d n := by
  have hBU := (CompactSpace.uniformContinuous_of_continuous (f := B) hB).comp_tendstoUniformly hu
  have hbounded : Bornology.IsBounded (range B) := (isCompact_range hB).isBounded
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  let d : ℕ → ℝ := fun n => sSup (insert 0 (range (fun x => ‖B (v x) - B (u n x)‖)))
  have hbdd (n : ℕ) : BddAbove (insert 0 (range (fun x => ‖B (v x) - B (u n x)‖))) := by
    refine ⟨max 0 (2 * C), ?_⟩
    rintro r (rfl | ⟨x, rfl⟩)
    · exact le_max_left _ _
    · have hvC := hC (B (v x)) ⟨v x, rfl⟩
      have huC := hC (B (u n x)) ⟨u n x, rfl⟩
      exact ((norm_sub_le (B (v x)) (B (u n x))).trans
        (show ‖B (v x)‖ + ‖B (u n x)‖ ≤ 2 * C by linarith)).trans (le_max_right _ _)
  have hd0 (n : ℕ) : 0 ≤ d n := le_csSup (hbdd n) (mem_insert _ _)
  have hdx (n : ℕ) (x : X) : ‖B (v x) - B (u n x)‖ ≤ d n :=
    le_csSup (hbdd n) (mem_insert_of_mem _ ⟨x, rfl⟩)
  refine ⟨d, ?_, hd0, hdx⟩
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall fun n => hr.trans_le (hd0 n)
  · intro r hr
    filter_upwards [(Metric.tendstoUniformly_iff
      (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hBU (r / 2) (by linarith)] with n hn
    have hdle : d n ≤ r / 2 := by
      apply csSup_le (insert_nonempty _ _)
      rintro z (rfl | ⟨x, rfl⟩)
      · linarith
      · have hx := hn x
        change dist (B (v x)) (B (u n x)) < r / 2 at hx
        rw [_root_.dist_eq_norm (B (v x)) (B (u n x))] at hx
        exact hx.le
    linarith

section Integral

variable {X Y : Type*} [MeasurableSpace X] {mu : Measure X}
  [UniformSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace E] [BorelSpace E]

local instance : MeasurableSpace (E →L[ℝ] E →L[ℝ] ℝ) := borel _
local instance : BorelSpace (E →L[ℝ] E →L[ℝ] ℝ) := ⟨rfl⟩



theorem suCompactRegularizedQuadratic_le_liminf
    (B : Y → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hpos : ∀ y v, v ≠ 0 → 0 < B y v v)
    {f : ℕ → X → Y} {f0 : X → Y}
    (hf : ∀ n, Measurable (f n)) (hf0 : Measurable f0)
    (hlim : TendstoUniformly f f0 atTop)
    (c : X → ℝ) (hc : Measurable c) (hc0 : ∀ x, 0 ≤ c x)
    {p : ℝ} (hp : 1 ≤ p)
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (u n)) atTop (𝓝 (L v))) :
    (∫⁻ x, ENNReal.ofReal (suRegularizedQuadratic (B (f0 x)) (c x) p (v x)) ∂mu) ≤
      liminf (fun n => ∫⁻ x,
        ENNReal.ofReal (suRegularizedQuadratic (B (f n x)) (c x) p (u n x)) ∂mu) atTop := by
  obtain ⟨a, ha, hcoerc⟩ := suCompactMetric_coercive isCompact_univ B hB.continuousOn
    (fun y _ v hv => hpos y v hv)
  obtain ⟨d, hd, hd0, hclose⟩ := suCompactMetric_uniform_errors B hB hlim
  refine suMovingRegularizedQuadratic_le_liminf _ _ (hB.measurable.comp hf0)
    (fun n => hB.measurable.comp (hf n)) ?_ ha
    (fun n x v => hcoerc (f n x) (mem_univ _) v) hd hd0 hclose c hc hc0 hp hw
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  · exact (hpos (f0 x) v hv).le

end Integral

end PoincareConjecture.M60
