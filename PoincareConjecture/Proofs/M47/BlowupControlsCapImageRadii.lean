import PoincareConjecture.Proofs.M47.BlowupControlsCapImageBalls
import PoincareConjecture.Proofs.M47.BlowupControlsCapCoreVolume
import PoincareConjecture.Proofs.M47.CanonicalNormalizedBallExistence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem exists_cap_image_core_radii
    {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X] [T3Space X] [CompactSpace X]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : CapCertificate g) (E : EpsilonNeck h) (D : LeviCivitaData h)
    (e : OpenPartialHomeomorph M X) (hsource : N.carrier ⊆ e.source)
    (hconnection : E.connection = D)
    (hcarrier : E.carrier = e '' N.end_neck.carrier)
    (hinverse : E.coordinate_inverse = N.end_neck.coordinate_inverse ∘ e.symm)
    (hpositive : ∀ x ∈ N.core, 0 < D.scalarCurvature (e x)) :
    ∃ r : X → ℝ, ∀ y ∈ e '' N.core,
      0 < r y ∧ scalarCurvatureSupOn h D (h.ball y (r y)) = (r y)⁻¹ ^ 2 ∧
      IsCompact (closure (h.ball y (r y))) ∧
      closure (h.ball y (r y)) ⊆ e '' N.carrier := by
  classical
  have hradii : ∀ y : X, ∃ r : ℝ, y ∈ e '' N.core →
      0 < r ∧ scalarCurvatureSupOn h D (h.ball y r) = r⁻¹ ^ 2 ∧
      IsCompact (closure (h.ball y r)) ∧ closure (h.ball y r) ⊆ e '' N.carrier := by
    intro y
    by_cases hy : y ∈ e '' N.core
    · obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨r, hr, _, hnorm, hcompact⟩ := Proofs.M47.exists_scalar_normalized_ball_on_compact
        h D (e x) (hpositive x hx)
      have hbounded : BddAbove (D.scalarCurvature '' h.ball (e x) r) :=
        (hcompact.image (M34.contMDiff_scalarCurvature D).continuous).bddAbove.mono
          (image_mono subset_closure)
      have hxclosed : x ∈ N.closed_core :=
        interior_subset (N.core_eq_interior_closed_core ▸ hx)
      have hcapture := scalar_normalized_cap_image_ball_captured N E D e hsource
        hconnection hcarrier hinverse (mem_image_of_mem e hxclosed) hr hbounded hnorm
      exact ⟨r, fun _ => ⟨hr, hnorm, hcapture⟩⟩
    · exact ⟨1, fun hmem => (hy hmem).elim⟩
  choose r hr using hradii
  exact ⟨r, hr⟩




theorem exists_cap_image_core_data_tolerance
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g) (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ w : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x w w) :
    ∃ Lambda : ℝ, 1 < Lambda ∧ ∃ nu : ℝ, 0 < nu ∧
      ∃ b' : ℝ, N.cap_constant⁻¹ < b' ∧
      ∀ {X : Type v} [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
        [MeasurableSpace X] [BorelSpace X] [T3Space X]
        [SecondCountableTopology X] [CompactSpace X]
        (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
        (e : OpenPartialHomeomorph M X),
      ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source →
      ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target → N.carrier ⊆ e.source →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
          Lambda * g.tangentNorm x w) →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        g.tangentNorm x w ≤
          Lambda * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w)) →
      (∀ x ∈ N.carrier, N.connection.scalarCurvature x ≤ D.scalarCurvature (e x) + nu) →
      ∀ E : EpsilonNeck h, E.connection = D →
        E.carrier = e '' N.end_neck.carrier →
        E.coordinate_inverse = N.end_neck.coordinate_inverse ∘ e.symm →
      ∃ r : X → ℝ, ∀ y ∈ e '' N.core,
        0 < r y ∧ scalarCurvatureSupOn h D (h.ball y (r y)) = (r y)⁻¹ ^ 2 ∧
        IsCompact (closure (h.ball y (r y))) ∧
        closure (h.ball y (r y)) ⊆ e '' N.carrier ∧
        ENNReal.ofReal (b' * r y ^ 3) ≤ calibratedMetricVolume h (h.ball y (r y)) := by
  obtain ⟨Lambda, hLambda, nu0, hnu0, b', hb', hvolume⟩ :=
    exists_cap_image_core_volume_tolerance N hcomplete hRic
  obtain ⟨m, hm, _, _, _, hfloor, _⟩ := Proofs.M47.cap_uniform_scalar_lower N
  let nu := min nu0 (m / 2)
  have hnu : 0 < nu := lt_min hnu0 (half_pos hm)
  refine ⟨Lambda, hLambda, nu, hnu, b', hb', ?_⟩
  intro X _ _ _ _ _ _ _ _ h D e hf hi hsource hupper hlower hscalar E hconnection
    hcarrier hinverse
  have hpositive (x : M) (hx : x ∈ N.core) : 0 < D.scalarCurvature (e x) := by
    have hxcarrier := N.core_subset_carrier' hx
    have hlow := hfloor x hxcarrier
    have hcompare := hscalar x hxcarrier
    have hsmall : nu ≤ m / 2 := min_le_right _ _
    linarith
  obtain ⟨r, hr⟩ := exists_cap_image_core_radii N E D e hsource hconnection hcarrier
    hinverse hpositive
  refine ⟨r, ?_⟩
  intro y hy
  have hdata := hr y hy
  refine ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, ?_⟩
  obtain ⟨x, hx, rfl⟩ := hy
  have hbounded : BddAbove (D.scalarCurvature '' h.ball (e x) (r (e x))) :=
    (hdata.2.2.1.image (M34.contMDiff_scalarCurvature D).continuous).bddAbove.mono
      (image_mono subset_closure)
  exact hvolume h D e hf hi hsource hupper hlower
    (fun z hz => (hscalar z hz).trans (add_le_add le_rfl (min_le_left _ _)))
    x hx (r (e x)) hdata.1 hbounded hdata.2.1

end PoincareConjecture.M47
