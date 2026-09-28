import PoincareConjecture.Proofs.M28.Sec10_6_Cone.EndRayAnnularDistortion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedMetricEndRayData











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}






theorem exists_selected_annular_approximation_maps
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
      (∀ p : U, r p < alpha → 0 < f p) →
      (∀ p : U, 0 < f p → ∃ gamma : ℝ → U,
        gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
        (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
          dist (gamma s) (gamma t) = |s - t|) ∧
        (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
        ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (A.inverse (gamma t)).2) →
      ∀ m : PseudoMetricSpace (MetricEndRay E alpha),
        letI := m
        CompactSpace (UniformSpace.Completion (MetricEndRay E alpha)) →
        (∀ P Q : MetricEndRay E alpha,
          ∀ s ∈ Ioo (0 : ℝ) P.length, ∀ t ∈ Ioo (0 : ℝ) Q.length,
            chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2) →
        (∀ P Q : MetricEndRay E alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
          (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
          (𝓝[>] (0 : ℝ)) (𝓝 (chordConeDistance r s (dist P Q)))) →
        ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
          (htriangle : ∀ x y z : UniformSpace.Completion (MetricEndRay E alpha),
            ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
              chordConeDistance r t (dist x z) ≤
                chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z)),
          letI := chordConeAnnulusMetric ha hab htriangle
          ∃ F : ℝ → U →
              ChordConeAnnulus (UniformSpace.Completion (MetricEndRay E alpha)) a b,
            (∀ (h : ℝ) (x : U), r x / h ∈ Icc a b →
              ((F h x).2 : ℝ) = r x / h) ∧
            ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
              ∀ x : U, r x / h ∈ Icc a b →
              ∀ y : U, r y / h ∈ Icc a b →
                0 ≤ dist (F h x) (F h y) - dist x y / h ∧
                  dist (F h x) (F h y) - dist x y / h < eta := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha halpha houtside
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  dsimp only
  intro hbarrier hproducer m
  let := m
  intro hcompact hupper hscaled a b ha hab htriangle
  let := hcompact
  let := chordConeAnnulusMetric ha hab htriangle
  have hdata : ∀ x : {x : U // r x < alpha / 4},
      ∃ P : MetricEndRay E alpha,
        P.length = r x.1 ∧ P.point P.length = x.1 := by
    intro x
    obtain ⟨P, hlength, hpoint, _hlower⟩ :=
      exists_selected_metricEndRay_at_point T A U f hfinite
        E alpha halpha houtside hbarrier hproducer x.1 x.2
    exact ⟨P, hlength, hpoint⟩
  choose P hlength hpoint using hdata
  obtain ⟨P₀, _Q₀, _hdifferent, _hP₀, _hQ₀⟩ :=
    exists_two_distinct_selected_metricEndRay_data T A U f hfinite
      E alpha halpha houtside hbarrier hproducer
  let datum (x : U) : MetricEndRay E alpha :=
    if hx : r x < alpha / 4 then P ⟨x, hx⟩ else P₀
  have hdatum (x : U) (hx : r x < alpha / 4) :
      (datum x).length = r x ∧ (datum x).point (datum x).length = x := by
    dsimp only [datum]
    rw [dif_pos hx]
    exact ⟨hlength ⟨x, hx⟩, hpoint ⟨x, hx⟩⟩
  let z₀ : ChordConeAnnulus
      (UniformSpace.Completion (MetricEndRay E alpha)) a b :=
    metricEndRayAnnularPoint P₀ ⟨a, le_rfl, hab⟩
  let F (h : ℝ) (x : U) : ChordConeAnnulus
      (UniformSpace.Completion (MetricEndRay E alpha)) a b :=
    if hx : r x / h ∈ Icc a b then
      metricEndRayAnnularPoint (datum x) ⟨r x / h, hx⟩
    else z₀
  have hF (h : ℝ) (x : U) (hx : r x / h ∈ Icc a b) :
      F h x = metricEndRayAnnularPoint (datum x) ⟨r x / h, hx⟩ := by
    dsimp only [F]
    rw [dif_pos hx]
  have hb : 0 < b := ha.trans_le hab
  have hsafe : 0 < alpha / (4 * b) :=
    div_pos halpha (mul_pos (by norm_num) hb)
  have hcap {h : ℝ} (hh : 0 < h) (hsmall : h < alpha / (4 * b))
      {x : U} (hx : r x / h ∈ Icc a b) : r x < alpha / 4 := by
    have hxbound : r x ≤ b * h := (div_le_iff₀ hh).mp hx.2
    have hbound : h * (4 * b) < alpha :=
      (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hb)).mp hsmall
    nlinarith only [hxbound, hbound]
  refine ⟨F, ?_, ?_⟩
  · intro h x hx
    rw [hF h x hx]
    rfl
  · intro eta heta
    have huniform := eventually_metricEndRay_annular_distortion
      (E := E) (alpha := alpha) ha hab htriangle hupper hscaled eta heta
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < alpha / (4 * b) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsafe)
    filter_upwards [huniform, hsmall, self_mem_nhdsWithin] with h huniform hsmall hh
    have hhpos : 0 < h := hh
    intro x hx y hy
    have hxdata := hdatum x (hcap hhpos hsmall hx)
    have hydata := hdatum y (hcap hhpos hsmall hy)
    let sx : Icc a b := ⟨r x / h, hx⟩
    let sy : Icc a b := ⟨r y / h, hy⟩
    have hxparameter : h * (sx : ℝ) = (datum x).length := by
      change h * (r x / h) = (datum x).length
      calc
        h * (r x / h) = (r x / h) * h := mul_comm _ _
        _ = r x := div_mul_cancel₀ _ hhpos.ne'
        _ = (datum x).length := hxdata.1.symm
    have hyparameter : h * (sy : ℝ) = (datum y).length := by
      change h * (r y / h) = (datum y).length
      calc
        h * (r y / h) = (r y / h) * h := mul_comm _ _
        _ = r y := div_mul_cancel₀ _ hhpos.ne'
        _ = (datum y).length := hydata.1.symm
    have hxpoint : (datum x).point (h * sx) = x := by
      rw [hxparameter]
      exact hxdata.2
    have hypoint : (datum y).point (h * sy) = y := by
      rw [hyparameter]
      exact hydata.2
    have hbound := huniform (datum x) (datum y) sx sy hxparameter.le hyparameter.le
    rw [hxpoint, hypoint] at hbound
    simpa only [hF h x hx, hF h y hy] using hbound

end PoincareConjecture.M28
