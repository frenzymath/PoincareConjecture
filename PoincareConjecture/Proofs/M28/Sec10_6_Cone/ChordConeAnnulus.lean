import PoincareConjecture.Proofs.M28.Mathlib.ChordConeDistance
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FunProp

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture.M28

theorem chordConeTriangle_completion
    {Y : Type*} [PseudoMetricSpace Y]
    (htriangle : ∀ x y z : Y, ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist x z) ≤
        chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z)) :
    ∀ x y z : UniformSpace.Completion Y, ∀ r s t : ℝ,
      0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist x z) ≤
        chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z) := by
  intro x y z r s t hr hs ht
  refine UniformSpace.Completion.induction_on₃ x y z ?_ ?_
  · apply isClosed_le
    · unfold chordConeDistance
      fun_prop
    · unfold chordConeDistance
      fun_prop
  · intro x y z
    simpa only [UniformSpace.Completion.dist_eq] using htriangle x y z r s t hr hs ht

theorem chord_bound_completion {Y : Type*} [PseudoMetricSpace Y] {B : ℝ}
    (hB : ∀ x y : Y, dist x y ≤ B) :
    ∀ x y : UniformSpace.Completion Y, dist x y ≤ B := by
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_le continuous_dist continuous_const
  · intro x y
    simpa only [UniformSpace.Completion.dist_eq] using hB x y

def ChordConeAnnulus (L : Type*) (a b : ℝ) := L × Icc a b

instance chordConeAnnulusTopologicalSpace {L : Type*} [TopologicalSpace L]
    {a b : ℝ} : TopologicalSpace (ChordConeAnnulus L a b) :=
  inferInstanceAs (TopologicalSpace (L × Icc a b))

section Annulus

variable {L : Type*} [MetricSpace L] {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (htriangle : ∀ x y z : L, ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist x z) ≤
        chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z))

@[instance_reducible]
def chordConeAnnulusMetric : MetricSpace (ChordConeAnnulus L a b) := by
  change MetricSpace (L × Icc a b)
  let d := fun x y : L × Icc a b =>
    chordConeDistance (x.2 : ℝ) (y.2 : ℝ) (dist x.1 y.1)
  have hrad (x y : L × Icc a b) : |(x.2 : ℝ) - y.2| ≤ d x y :=
    abs_sub_le_chordConeDistance (ha.le.trans x.2.property.1)
      (ha.le.trans y.2.property.1)
  have hlink (x y : L × Icc a b) : a * dist x.1 y.1 ≤ d x y :=
    mul_le_chordConeDistance ha.le x.2.property.1 y.2.property.1
  have hupper (x y : L × Icc a b) : d x y ≤ (1 + b) * dist x y := by
    have h := chordConeDistance_le_abs_sub_add_mul
      (ha.le.trans x.2.property.1) (ha.le.trans y.2.property.1)
      x.2.property.2 y.2.property.2 (dist_nonneg (x := x.1) (y := y.1))
    have h1 : dist x.1 y.1 ≤ dist x y := le_max_left _ _
    have h2 : |(x.2 : ℝ) - y.2| ≤ dist x y := by
      simpa only [Prod.dist_eq, Subtype.dist_eq, Real.dist_eq] using
        (le_max_right (dist x.1 y.1) (dist x.2 y.2))
    have hmul := mul_le_mul_of_nonneg_left h1 (ha.le.trans hab)
    dsimp only [d]
    nlinarith only [h, h2, hmul]
  refine MetricSpace.ofDistTopology d ?_ ?_ ?_ ?_ ?_
  · intro x
    dsimp only [d]
    rw [dist_self, chordConeDistance_self]
  · intro x y
    dsimp only [d]
    rw [chordConeDistance_comm, dist_comm]
  · intro x y z
    exact htriangle x.1 y.1 z.1 x.2 y.2 z.2
      (ha.trans_le x.2.property.1) (ha.trans_le y.2.property.1)
      (ha.trans_le z.2.property.1)
  · intro S
    constructor
    · intro hS x hx
      obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hS x hx
      refine ⟨min a 1 * epsilon, mul_pos (lt_min ha zero_lt_one) hepsilon, ?_⟩
      intro y hxy
      apply hball
      rw [Metric.mem_ball, dist_comm, Prod.dist_eq]
      apply max_lt
      · have hl : d x y < a * epsilon :=
          hxy.trans_le (mul_le_mul_of_nonneg_right (min_le_left a 1) hepsilon.le)
        exact (mul_lt_mul_iff_of_pos_left ha).mp ((hlink x y).trans_lt hl)
      · rw [Subtype.dist_eq, Real.dist_eq]
        have hl : d x y < epsilon := by
          have hh := hxy.trans_le
            (mul_le_mul_of_nonneg_right (min_le_right a 1) hepsilon.le)
          simpa only [one_mul] using hh
        exact (hrad x y).trans_lt hl
    · intro hS
      apply Metric.isOpen_iff.mpr
      intro x hx
      obtain ⟨epsilon, hepsilon, hball⟩ := hS x hx
      have hb : 0 < 1 + b := by linarith only [ha, hab]
      refine ⟨epsilon / (1 + b), div_pos hepsilon hb, ?_⟩
      intro y hy
      apply hball y
      have hy' : dist x y < epsilon / (1 + b) := by
        simpa only [Metric.mem_ball, dist_comm] using hy
      have hsmall := (lt_div_iff₀ hb).mp hy'
      have hu := hupper x y
      nlinarith only [hsmall, hu]
  · intro x y hxy
    have hr : (x.2 : ℝ) = y.2 := by
      have hh := hrad x y
      rw [hxy] at hh
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
    have hl : dist x.1 y.1 = 0 := by
      have hh := hlink x y
      rw [hxy] at hh
      have hn : 0 ≤ dist x.1 y.1 := dist_nonneg
      nlinarith only [ha, hh, hn]
    exact Prod.ext (dist_eq_zero.mp hl) (Subtype.ext hr)

theorem chordConeAnnulus_dist_eq (x y : ChordConeAnnulus L a b) :
    letI := chordConeAnnulusMetric ha hab htriangle
    dist x y = chordConeDistance (x.2 : ℝ) (y.2 : ℝ) (dist x.1 y.1) := rfl

theorem chordConeAnnulus_compact [CompactSpace L] :
    letI := chordConeAnnulusMetric ha hab htriangle
    CompactSpace (ChordConeAnnulus L a b) := by
  exact (inferInstance : CompactSpace (L × Icc a b))

theorem chordConeAnnulus_radius_lipschitz :
    letI := chordConeAnnulusMetric ha hab htriangle
    LipschitzWith 1 (fun x : ChordConeAnnulus L a b => (x.2 : ℝ)) := by
  let := chordConeAnnulusMetric ha hab htriangle
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |(x.2 : ℝ) - y.2| ≤ (1 : ℝ) *
    chordConeDistance (x.2 : ℝ) (y.2 : ℝ) (dist x.1 y.1)
  simpa only [one_mul] using
    (abs_sub_le_chordConeDistance (d := dist x.1 y.1)
      (ha.le.trans x.2.property.1) (ha.le.trans y.2.property.1))

theorem chordConeAnnulus_local_radial_variation (x z y : ChordConeAnnulus L a b)
    (hz : (z.2 : ℝ) ∈ Ioo a b) :
    letI := chordConeAnnulusMetric ha hab htriangle
    ∀ᶠ c : ℝ in 𝓝 1, ∃ w : ChordConeAnnulus L a b,
      dist x w ^ 2 = c ^ 2 * (z.2 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2 -
        c * ((z.2 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2 - dist x z ^ 2) ∧
      dist y w ^ 2 = c ^ 2 * (z.2 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 -
        c * ((z.2 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - dist y z ^ 2) := by
  let := chordConeAnnulusMetric ha hab htriangle
  have hmap : Tendsto (fun c : ℝ => c * (z.2 : ℝ)) (𝓝 1) (𝓝 (z.2 : ℝ)) := by
    simpa only [id_eq, one_mul] using
      (tendsto_id : Tendsto (fun c : ℝ => c) (𝓝 1) (𝓝 1)).mul
        (tendsto_const_nhds (x := (z.2 : ℝ)))
  filter_upwards [hmap.eventually (Ioo_mem_nhds hz.1 hz.2),
    Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc hpositive
  let w : ChordConeAnnulus L a b := (z.1, ⟨c * (z.2 : ℝ), hc.1.le, hc.2.le⟩)
  refine ⟨w, ?_, ?_⟩
  · exact chordConeDistance_dilation_sq (d := dist x.1 z.1)
      (ha.le.trans x.2.property.1) (ha.le.trans z.2.property.1) hpositive.le
  · exact chordConeDistance_dilation_sq (d := dist y.1 z.1)
      (ha.le.trans y.2.property.1) (ha.le.trans z.2.property.1) hpositive.le

end Annulus

end PoincareConjecture.M28
