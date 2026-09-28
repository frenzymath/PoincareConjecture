import PoincareConjecture.Proofs.M10.ActionEquality
import PoincareConjecture.Proofs.M10.ExponentialActionDerivative









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponential_velocity_eq_radial
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (ha : ∀ y : EuclideanSpace ℝ (Fin n),
      G.toLExponentialFamily.action (metricCoordinates (F.metric T) p y) τ /
        (2 * Real.sqrt τ) = ‖y‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin n))
    (hgram : ∀ u v : EuclideanSpace ℝ (Fin n),
      pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x u v =
        4 * τ * inner ℝ u v)
    (hcrit : Function.Surjective
      (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ)) :
    curveVelocity (G.gamma (metricCoordinates (F.metric T) p x)) τ =
      G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
        ((2 * τ)⁻¹ • metricCoordinates (F.metric T) p x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := metricCoordinates (F.metric T) p
  let q := G.gamma (β x) τ
  let D := G.toLExponentialFamily.sliceDifferential (β x) τ
  let U := curveVelocity (n := n) (G.gamma (β x)) τ
  let V := D ((2 * τ)⁻¹ • β x)
  have hpair (v : EuclideanSpace ℝ (Fin n)) :
      (F.metric (T - τ)).inner q U (D (β v)) = 2 * inner ℝ x v :=
    exponential_velocity_pairing_of_quadratic_action G hτ hmax ha x v
  have hradial (v : EuclideanSpace ℝ (Fin n)) :
      (F.metric (T - τ)).inner q V (D (β v)) = 2 * inner ℝ x v := by
    have h := hgram ((2 * τ)⁻¹ • x) v
    change (F.metric (T - τ)).inner (exponentialSliceChart G τ x)
      (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x ((2 * τ)⁻¹ • x))
      (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x v) = _ at h
    rw [exponentialSliceChart_differential G hτ hmax,
      exponentialSliceChart_differential G hτ hmax, exponentialSliceChart_apply,
      map_smul, inner_smul_left] at h
    change (F.metric (T - τ)).inner q V (D (β v)) = _ at h
    rw [h]
    simp only [conj_trivial]
    field_simp
    ring
  have hpairing (w : TangentSpace (𝓡 n) q) :
      (F.metric (T - τ)).inner q U w = (F.metric (T - τ)).inner q V w := by
    obtain ⟨W, hW⟩ := hcrit w
    obtain ⟨v, hv⟩ := β.surjective W
    rw [← hW, ← hv]
    exact (hpair v).trans (hradial v).symm
  change U = V
  by_contra hne
  have hpos := (F.metric (T - τ)).pos q (U - V) (sub_ne_zero.mpr hne)
  have hzero : (F.metric (T - τ)).inner q (U - V) (U - V) = 0 := by
    rw [map_sub]
    rw [(F.metric (T - τ)).symm q (U - V) U,
      (F.metric (T - τ)).symm q (U - V) V]
    exact sub_eq_zero.mpr (hpairing (U - V))
  linarith only [hpos, hzero]

variable [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem exponential_velocity_eq_radial_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    curveVelocity (G.gamma (metricCoordinates (F.metric T) p x)) τ =
      G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
        ((2 * τ)⁻¹ • metricCoordinates (F.metric T) p x) := by
  have heqτ := reducedVolume_eq_euclidean_of_le hL hDifferential G hmax hT hwindow
    hcurvature hb hbmax hτ hτb.le heq
  have hsource := (exponentialSliceChart_global_of_volume_eq hL hDifferential G hmax hT
    hwindow hcurvature hτ (hτb.trans hbmax) heqτ).1
  have hreg : (metricCoordinates (F.metric T) p x, τ) ∈
      G.toLExponentialFamily.regularDomain := by
    have hx : x ∈ (exponentialSliceChart G τ).source := hsource.symm ▸ mem_univ x
    simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hx
  exact exponential_velocity_eq_radial G hτ (hτb.trans hbmax)
    (fun y ↦ normalized_action_eq_norm_sq_of_volume_eq hL hDifferential G hmax hT hwindow
      hcurvature hb hbmax heq y hτ hτb) x
    (fun u v ↦ exponential_pairing_eq_of_volume_eq hL hDifferential G hmax hT hwindow
      hcurvature hb hbmax heq x u v hτ hτb) hreg.2.2

end PoincareConjecture.M10
