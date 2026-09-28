import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.ClosedRegions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeRegion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem exists_closed_tube_region (e : TerminalEnd K)
    (A : RepairedNeckCapTopologyTheory.{u})
    {epsilon C B : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hle : epsilon ≤ A.epsilon₀)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (hcanonical : ∀ x : (E.extended.slice T).carrier,
      B < (E.extended.connection T).scalarCurvature x →
        GeneralizedCanonicalControl (F := E.extended) T x epsilon C)
    (D : ℝ) :
    ∃ n : ℕ, ∃ Y : Set (E.extended.slice T).carrier,
      IsClosed Y ∧ IsCompact (frontier Y) ∧ Subtype.val '' e.tail n ⊆ Y ∧
      Y ⊆ K.component ∧
      (∀ x ∈ Y, D ≤ (E.extended.connection T).scalarCurvature x) ∧
      ∃ tube : EpsilonTubeCertificate (E.extended.metric T) Y,
        tube.epsilon = epsilon := by
  let : LocallyCompactSpace (E.extended.slice T).carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
  obtain ⟨n, X, hXclosed, hXconnected, htail, hXK, hscalar, _, hfront⟩ :=
    e.exists_closed_scalar_region hlower hproper (max (B + 1) D)
  have hcontrol : ∀ x ∈ X,
      GeneralizedCanonicalControl (F := E.extended) T x epsilon C := by
    intro x hx
    apply hcanonical x
    have := (le_max_left (B + 1) D).trans (hscalar x hx)
    linarith
  let H := e.neckCapCoverOn X hXconnected hXK hepsilon hC A.epsilon₀_pos
    A.epsilon₀_le_one_two_hundred hle hcontrol
  obtain ⟨region⟩ := A.a21 (E.extended.metric T) H hle
  obtain ⟨R, hR⟩ := region
  cases R with
  | twoCaps kind cap₁ cap₂ component union_eq contains_X =>
      exact (e.tail_image_not_subset_compact n component.compact
        (htail.trans contains_X)).elim
  | doubleCappedTube certificate kind component contains_X =>
      exact (e.tail_image_not_subset_compact n certificate.compact
        (htail.trans contains_X)).elim
  | singleCap cap contains_X =>
      exact (e.tail_image_not_subset_compact n
        (cap.isCompact_closure_of_scalar_proper (E.extended.connection T) hproper)
        ((htail.trans contains_X).trans subset_closure)).elim
  | fibration fibration =>
      exact (e.tail_image_not_subset_compact n fibration.compact
        (htail.trans fibration.contains_X)).elim
  | tube tube =>
      exact ⟨n, X, hXclosed, hfront, htail, hXK,
        fun x hx => (le_max_right (B + 1) D).trans (hscalar x hx), tube, hR⟩
  | cappedTube certificate contains_X =>
      have hcap := certificate.cap.isCompact_closure_of_scalar_proper
        (E.extended.connection T) hproper
      obtain ⟨V, hV, hcapV, _, hVcompact⟩ :=
        exists_open_between_and_isCompact_closure hcap isOpen_univ (subset_univ _)
      obtain ⟨k, hk⟩ := e.exists_tail_disjoint_compact hVcompact
      let m := max n k
      let Y := X \ V
      have hYclosed : IsClosed Y := hXclosed.sdiff hV
      have hYfront : IsCompact (frontier Y) := by
        apply (hfront.union hVcompact).of_isClosed_subset isClosed_frontier
        intro x hx
        have := frontier_inter_subset X Vᶜ hx
        rcases this with hxX | hxV
        · exact Or.inl hxX.1
        · exact Or.inr (frontier_subset_closure (by simpa using hxV.2))
      have htailY : Subtype.val '' e.tail m ⊆ Y := by
        intro x hx
        refine ⟨htail (Set.image_mono (e.nested (le_max_left n k)) hx), ?_⟩
        exact fun hxV => Set.disjoint_left.mp (hk m (le_max_right n k)) hx
          (subset_closure hxV)
      have hYtube : Y ⊆ certificate.tube.carrier := by
        rintro x ⟨hxX, hxV⟩
        have hx := contains_X hxX
        rw [certificate.carrier_eq_union] at hx
        exact hx.resolve_left (fun hxcap => hxV (hcapV (subset_closure hxcap)))
      refine ⟨m, Y, hYclosed, hYfront, htailY, sdiff_subset.trans hXK,
        fun x hx => (le_max_right (B + 1) D).trans (hscalar x hx.1),
        { certificate.tube with contains_X := hYtube }, ?_⟩
      exact hR.2.1

end PoincareConjecture.TerminalEnd
