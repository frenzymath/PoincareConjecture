import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.NeckCapCover









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}



theorem exists_tube_of_neckCapRegion (e : TerminalEnd K) (n : ℕ)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (H : ConnectedNeckCapCover (E.extended.metric T))
    (hX : H.X = Subtype.val '' e.tail n)
    (R : NeckCapRegion (E.extended.metric T) H.X)
    (hR : NeckCapRegionCompatible (E.extended.metric T) H R) :
    ∃ m : ℕ, n ≤ m ∧
      ∃ tube : EpsilonTubeCertificate (E.extended.metric T) (Subtype.val '' e.tail m),
        tube.epsilon = H.epsilon := by
  cases R with
  | twoCaps kind cap₁ cap₂ component union_eq contains_X =>
      exact (e.tail_image_not_subset_compact n component.compact
        (hX ▸ contains_X)).elim
  | doubleCappedTube certificate kind component contains_X =>
      exact (e.tail_image_not_subset_compact n certificate.compact
        (hX ▸ contains_X)).elim
  | singleCap cap contains_X =>
      exact (e.tail_image_not_subset_compact n
        (cap.isCompact_closure_of_scalar_proper (E.extended.connection T) hproper)
        ((hX ▸ contains_X).trans subset_closure)).elim
  | fibration fibration =>
      exact (e.tail_image_not_subset_compact n fibration.compact
        (hX ▸ fibration.contains_X)).elim
  | tube tube =>
      exact ⟨n, le_rfl, { tube with contains_X := hX ▸ tube.contains_X }, hR⟩
  | cappedTube certificate contains_X =>
      obtain ⟨k, hk⟩ := e.exists_tail_disjoint_cap hproper certificate.cap
      let m := max n k
      have hsub : Subtype.val '' e.tail m ⊆ certificate.tube.carrier := by
        rintro x ⟨y, hy, rfl⟩
        have hyn : y ∈ e.tail n := e.nested (le_max_left n k) hy
        have hmem : (y : (E.extended.slice T).carrier) ∈ certificate.carrier :=
          contains_X (hX ▸ ⟨y, hyn, rfl⟩)
        rw [certificate.carrier_eq_union] at hmem
        rcases hmem with hcap | htube
        · exact (Set.disjoint_left.mp (hk m (le_max_right n k)) ⟨y, hy, rfl⟩ hcap).elim
        · exact htube
      exact ⟨m, le_max_left n k, { certificate.tube with contains_X := hsub }, hR.2.1⟩



theorem exists_tube_of_canonical_control (e : TerminalEnd K)
    (A : RepairedNeckCapTopologyTheory.{u})
    {epsilon C B : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hle : epsilon ≤ A.epsilon₀)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (hcanonical : ∀ x : (E.extended.slice T).carrier,
      B < (E.extended.connection T).scalarCurvature x →
        GeneralizedCanonicalControl (F := E.extended) T x epsilon C) :
    ∃ n : ℕ,
      ∃ tube : EpsilonTubeCertificate (E.extended.metric T) (Subtype.val '' e.tail n),
        tube.epsilon = epsilon := by
  obtain ⟨n, H, hX, he, _⟩ := e.exists_neckCapCover hepsilon hC A.epsilon₀_pos
    A.epsilon₀_le_one_two_hundred hle hlower hproper hcanonical
  obtain ⟨D⟩ := A.a21 (E.extended.metric T) H (he ▸ hle)
  obtain ⟨m, _, tube, htube⟩ :=
    e.exists_tube_of_neckCapRegion n hproper H hX D.region D.compatible
  exact ⟨m, tube, htube.trans he⟩

end PoincareConjecture.TerminalEnd
