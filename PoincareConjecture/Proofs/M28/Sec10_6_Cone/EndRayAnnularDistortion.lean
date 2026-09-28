import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayEndpoint
import PoincareConjecture.Proofs.M28.Mathlib.ChordConeDistanceScaling
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.ChordConeAnnulus
import Mathlib.Order.Filter.Finite










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M28

variable {X : Type u} [MetricSpace X]
  {E : UniformSpace.Completion X} {alpha : ℝ}
  [PseudoMetricSpace (MetricEndRay E alpha)]



def metricEndRayAnnularPoint {a b : ℝ} (P : MetricEndRay E alpha)
    (s : Icc a b) :
    ChordConeAnnulus (UniformSpace.Completion (MetricEndRay E alpha)) a b :=
  ((P : UniformSpace.Completion (MetricEndRay E alpha)), s)

section Annulus

variable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
  (htriangle : ∀ x y z : UniformSpace.Completion (MetricEndRay E alpha),
    ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist x z) ≤
        chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z))



theorem metricEndRayAnnularPoint_dist
    (P Q : MetricEndRay E alpha) (s t : Icc a b) :
    letI := chordConeAnnulusMetric ha hab htriangle
    dist (metricEndRayAnnularPoint P s) (metricEndRayAnnularPoint Q t) =
      chordConeDistance s t (dist P Q) := by
  let := chordConeAnnulusMetric ha hab htriangle
  rw [chordConeAnnulus_dist_eq ha hab htriangle]
  simp only [metricEndRayAnnularPoint, UniformSpace.Completion.dist_eq]




theorem metricEndRay_annular_scaled_dist_le
    (hupper : ∀ P Q : MetricEndRay E alpha,
      ∀ s ∈ Ioo (0 : ℝ) P.length, ∀ t ∈ Ioo (0 : ℝ) Q.length,
        chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2)
    (P Q : MetricEndRay E alpha) (s t : Icc a b) {h : ℝ}
    (hh : 0 < h) (hP : h * (s : ℝ) ≤ P.length)
    (hQ : h * (t : ℝ) ≤ Q.length) :
    letI := chordConeAnnulusMetric ha hab htriangle
    dist (P.point (h * s)) (Q.point (h * t)) / h ≤
      dist (metricEndRayAnnularPoint P s) (metricEndRayAnnularPoint Q t) := by
  let := chordConeAnnulusMetric ha hab htriangle
  have hs : h * (s : ℝ) ∈ Ioc (0 : ℝ) P.length :=
    ⟨mul_pos hh (ha.trans_le s.property.1), hP⟩
  have ht : h * (t : ℝ) ∈ Ioc (0 : ℝ) Q.length :=
    ⟨mul_pos hh (ha.trans_le t.property.1), hQ⟩
  have hb := P.dist_le_chordConeDistance Q (hupper P Q)
    (h * s) hs (h * t) ht
  rw [chordConeDistance_mul h hh.le] at hb
  rw [metricEndRayAnnularPoint_dist ha hab htriangle]
  exact (div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hb)



theorem exists_finite_metricEndRay_annular_net
    [CompactSpace (UniformSpace.Completion (MetricEndRay E alpha))]
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    letI := chordConeAnnulusMetric ha hab htriangle
    ∃ F : Finset (MetricEndRay E alpha × Icc a b),
      ∀ z : ChordConeAnnulus (UniformSpace.Completion (MetricEndRay E alpha)) a b,
        ∃ i ∈ F, dist z (metricEndRayAnnularPoint i.1 i.2) < epsilon := by
  classical
  let := chordConeAnnulusMetric ha hab htriangle
  let : CompactSpace (ChordConeAnnulus
      (UniformSpace.Completion (MetricEndRay E alpha)) a b) := chordConeAnnulus_compact
  have hdense : DenseRange (fun i : MetricEndRay E alpha × Icc a b =>
      metricEndRayAnnularPoint i.1 i.2) := by
    change DenseRange (Prod.map
      ((↑) : MetricEndRay E alpha →
        UniformSpace.Completion (MetricEndRay E alpha)) (id : Icc a b → Icc a b))
    exact UniformSpace.Completion.denseRange_coe.prodMap denseRange_id
  let O (i : MetricEndRay E alpha × Icc a b) :=
    Metric.ball (metricEndRayAnnularPoint i.1 i.2) epsilon
  have hcover : (univ : Set (ChordConeAnnulus
      (UniformSpace.Completion (MetricEndRay E alpha)) a b)) ⊆ ⋃ i, O i := by
    intro z _hz
    obtain ⟨i, hi⟩ := hdense.exists_dist_lt z hepsilon
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨F, fun z => ?_⟩
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hF (mem_univ z))
  exact ⟨i, hi, hzi⟩




theorem eventually_metricEndRay_annular_distortion
    [CompactSpace (UniformSpace.Completion (MetricEndRay E alpha))]
    (hupper : ∀ P Q : MetricEndRay E alpha,
      ∀ s ∈ Ioo (0 : ℝ) P.length, ∀ t ∈ Ioo (0 : ℝ) Q.length,
        chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2)
    (hscaled : ∀ P Q : MetricEndRay E alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
      (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (chordConeDistance r s (dist P Q)))) :
    letI := chordConeAnnulusMetric ha hab htriangle
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ P Q : MetricEndRay E alpha, ∀ s t : Icc a b,
        h * (s : ℝ) ≤ P.length → h * (t : ℝ) ≤ Q.length →
        0 ≤ dist (metricEndRayAnnularPoint P s) (metricEndRayAnnularPoint Q t) -
          dist (P.point (h * s)) (Q.point (h * t)) / h ∧
        dist (metricEndRayAnnularPoint P s) (metricEndRayAnnularPoint Q t) -
          dist (P.point (h * s)) (Q.point (h * t)) / h < eta := by
  classical
  let := chordConeAnnulusMetric ha hab htriangle
  intro eta heta
  let epsilon := eta / 8
  have hepsilon : 0 < epsilon := div_pos heta (by norm_num)
  obtain ⟨F, hF⟩ := exists_finite_metricEndRay_annular_net
    ha hab htriangle epsilon hepsilon
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
  have hlength : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ i ∈ F, h * b < i.1.length := by
    apply F.eventually_all.mpr
    intro i _hi
    have hmul : Tendsto (fun h : ℝ => h * b)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using hid.mul_const b
    exact hmul.eventually (Iio_mem_nhds i.1.length_pos)
  have hpairs : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ i ∈ F, ∀ j ∈ F,
        dist (metricEndRayAnnularPoint i.1 i.2) (metricEndRayAnnularPoint j.1 j.2) <
          dist (i.1.point (h * i.2)) (j.1.point (h * j.2)) / h + epsilon := by
    apply F.eventually_all.mpr
    intro i _hi
    apply F.eventually_all.mpr
    intro j _hj
    have hij : Tendsto
        (fun h : ℝ => dist (i.1.point (h * i.2)) (j.1.point (h * j.2)) / h)
        (𝓝[>] (0 : ℝ))
        (𝓝 (dist (metricEndRayAnnularPoint i.1 i.2)
          (metricEndRayAnnularPoint j.1 j.2))) := by
      rw [metricEndRayAnnularPoint_dist ha hab htriangle]
      exact hscaled i.1 j.1 i.2 j.2
        (ha.trans_le i.2.property.1) (ha.trans_le j.2.property.1)
    filter_upwards [hij.eventually (Ioi_mem_nhds
      (show dist (metricEndRayAnnularPoint i.1 i.2)
          (metricEndRayAnnularPoint j.1 j.2) - epsilon <
        dist (metricEndRayAnnularPoint i.1 i.2)
          (metricEndRayAnnularPoint j.1 j.2) by linarith only [hepsilon]))] with h hh
    linarith only [hh]
  filter_upwards [self_mem_nhdsWithin, hlength, hpairs] with h hh hlength hpairs
  have hhpos : 0 < h := hh
  intro P Q s t hP hQ
  have hforward := metricEndRay_annular_scaled_dist_le
    ha hab htriangle hupper P Q s t hhpos hP hQ
  refine ⟨sub_nonneg.mpr hforward, ?_⟩
  obtain ⟨i, hi, hPi⟩ := hF (metricEndRayAnnularPoint P s)
  obtain ⟨j, hj, hQj⟩ := hF (metricEndRayAnnularPoint Q t)
  have hiLength : h * (i.2 : ℝ) ≤ i.1.length :=
    (mul_le_mul_of_nonneg_left i.2.property.2 hhpos.le).trans (hlength i hi).le
  have hjLength : h * (j.2 : ℝ) ≤ j.1.length :=
    (mul_le_mul_of_nonneg_left j.2.property.2 hhpos.le).trans (hlength j hj).le
  have hsourcePi : dist (P.point (h * s)) (i.1.point (h * i.2)) / h < epsilon :=
    (metricEndRay_annular_scaled_dist_le ha hab htriangle hupper
      P i.1 s i.2 hhpos hP hiLength).trans_lt hPi
  have hsourceQj : dist (Q.point (h * t)) (j.1.point (h * j.2)) / h < epsilon :=
    (metricEndRay_annular_scaled_dist_le ha hab htriangle hupper
      Q j.1 t j.2 hhpos hQ hjLength).trans_lt hQj
  have hsourceiP : dist (i.1.point (h * i.2)) (P.point (h * s)) / h < epsilon := by
    simpa only [dist_comm] using hsourcePi
  have hjQ : dist (metricEndRayAnnularPoint j.1 j.2)
      (metricEndRayAnnularPoint Q t) < epsilon := by
    simpa only [dist_comm] using hQj
  have hsourceTriangle :
      dist (i.1.point (h * i.2)) (j.1.point (h * j.2)) / h ≤
        dist (i.1.point (h * i.2)) (P.point (h * s)) / h +
        dist (P.point (h * s)) (Q.point (h * t)) / h +
        dist (Q.point (h * t)) (j.1.point (h * j.2)) / h := by
    simpa only [add_div] using div_le_div_of_nonneg_right
      (dist_triangle4 (i.1.point (h * i.2)) (P.point (h * s))
        (Q.point (h * t)) (j.1.point (h * j.2))) hhpos.le
  have hconeTriangle := dist_triangle4 (metricEndRayAnnularPoint P s)
    (metricEndRayAnnularPoint i.1 i.2) (metricEndRayAnnularPoint j.1 j.2)
    (metricEndRayAnnularPoint Q t)
  have hfixed := hpairs i hi j hj
  have herror :
      dist (metricEndRayAnnularPoint P s) (metricEndRayAnnularPoint Q t) -
        dist (P.point (h * s)) (Q.point (h * t)) / h < 5 * epsilon := by
    linarith only [hconeTriangle, hPi, hjQ, hfixed,
      hsourceTriangle, hsourceiP, hsourceQj]
  dsimp only [epsilon] at herror
  linarith only [herror, heta]

end Annulus

end PoincareConjecture.M28
