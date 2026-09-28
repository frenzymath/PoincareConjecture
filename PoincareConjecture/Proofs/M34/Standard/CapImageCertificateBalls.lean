import PoincareConjecture.Proofs.M34.Standard.CapBallVolume
import PoincareConjecture.Proofs.M34.Standard.CapQuantitativeBounds
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlCapBalls

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
  [T3Space M] [T3Space X] [SecondCountableTopology M] [SecondCountableTopology X]
  [ConnectedSpace M] [ConnectedSpace X]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem exists_image_recut_core_radii
    {C : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h) (hcomplete' : MetricComplete h)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 8)
    (haccuracy : N.epsilon < epsilon)
    (hsource : N.carrier ⊆ e.source)
    (hcapture : closure (N.recutCarrier (2 / epsilon - N.epsilon⁻¹)) ⊆ e.source)
    (hupper : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * g.tangentNorm x v)
    (hlower : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 2 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v))
    (hscalar : ∀ x ∈ N.recutCarrier (2 / epsilon - N.epsilon⁻¹),
      |D.scalarCurvature (e x) - N.connection.scalarCurvature x| ≤ (2 * C)⁻¹)
    (hboundary : ∀ x ∈ N.boundary_sphere,
      (2 * N.end_neck.scale ^ 2)⁻¹ ≤ D.scalarCurvature (e x)) :
    ∃ r : X → ℝ, ∀ y ∈ e '' N.core,
      0 < r y ∧ scalarCurvatureSupOn h D (h.ball y (r y)) = (r y)⁻¹ ^ 2 ∧
      IsCompact (closure (h.ball y (r y))) ∧
      closure (h.ball y (r y)) ⊆ e '' N.recutCarrier (2 / epsilon - N.epsilon⁻¹) ∧
      ENNReal.ofReal (M34.capBallVolumeCoefficient C * r y ^ 3) ≤
        calibratedMetricVolume h (h.ball y (r y)) := by
  classical
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hvalues := N.scalar_bounds_on_image_of_close hC1 hC ho hnormal D e
    (N.recutCarrier_subset_carrier (2 / epsilon - N.epsilon⁻¹)) hscalar
  have hradii : ∀ y : X, ∃ r : ℝ, y ∈ e '' N.core →
      0 < r ∧ scalarCurvatureSupOn h D (h.ball y r) = r⁻¹ ^ 2 ∧
      IsCompact (closure (h.ball y r)) ∧
      closure (h.ball y r) ⊆ e '' N.recutCarrier (2 / epsilon - N.epsilon⁻¹) ∧
      ENNReal.ofReal (M34.capBallVolumeCoefficient C * r ^ 3) ≤
        calibratedMetricVolume h (h.ball y r) := by
    intro y
    by_cases hy : y ∈ e '' N.core
    · obtain ⟨x, hx, rfl⟩ := hy
      have hxclosed : x ∈ N.closed_core :=
        interior_subset (N.core_eq_interior_closed_core ▸ hx)
      have hximage : e x ∈ e '' N.recutCarrier (2 / epsilon - N.epsilon⁻¹) :=
        ⟨x, Or.inl hxclosed, rfl⟩
      have hpositive : 0 < D.scalarCurvature (e x) :=
        (inv_pos.mpr (by positivity : 0 < 2 * C)).trans_le (hvalues _ hximage).1
      obtain ⟨r, hr, _, hnorm, hcompact, hsubset⟩ :=
        N.exists_normalized_ball_in_standard_recut_image h hcomplete' e hf hi
          hepsilon hsmall haccuracy hcapture (fun z hz => hlower z (hcapture hz))
          (M34.contMDiff_scalarCurvature D).continuous hboundary hxclosed hpositive
      have hnorm' : scalarCurvatureSupOn h D (h.ball (e x) r) = r⁻¹ ^ 2 := by
        simpa only [scalarCurvatureSupOn, image_eq_range] using hnorm
      have hvolume := N.normalized_image_core_ball_volume_lower hC1 hC hcomplete hRic
        ho hnormal h D e hf hi hsource hupper hlower hx hr hnorm'
        (fun z hz => hvalues z (hsubset (subset_closure hz)))
      exact ⟨r, fun _ => ⟨hr, hnorm', hcompact, hsubset, hvolume⟩⟩
    · exact ⟨1, fun hmem => (hy hmem).elim⟩
  choose r hr using hradii
  exact ⟨r, hr⟩

end PoincareConjecture.CapCertificate
