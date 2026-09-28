import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCapCover

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

theorem StandardPuncturedProjectiveCover.not_isCompact_region
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    {p : RealProjectiveThree} {U : Set M}
    (P : PoincareConjecture.StandardPuncturedProjectiveCover M p U)
    (hne : U.Nonempty) : ¬ IsCompact U := by
  intro hcompact
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace UnitThreeSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have hdomain : IsCompact (univ : Set (projectiveCoverDomain p)) := by
    simpa only [preimage_univ] using
      (StandardPuncturedProjectiveCover.restrictedCover_isProperMap P).isCompact_preimage
        (isCompact_univ : IsCompact (univ : Set U))
  have hclosed : IsClosed (projectiveCoverDomain p) := by
    have himage : (Subtype.val : projectiveCoverDomain p → UnitThreeSphere) '' univ =
        projectiveCoverDomain p := by
      ext x
      constructor
      · rintro ⟨y, _, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
    rw [← himage]
    exact (hdomain.image continuous_subtype_val).isClosed
  have hdomain_ne : (projectiveCoverDomain p).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, hx, _⟩ := P.image_eq.symm.subset hy
    exact ⟨x, hx⟩
  have hfull : projectiveCoverDomain p = univ :=
    (show IsClopen (projectiveCoverDomain p) from
      ⟨hclosed, isOpen_projectiveCoverDomain p⟩).eq_univ hdomain_ne
  obtain ⟨x, hx⟩ := Quotient.mk'_surjective p
  have hxvalid : x ∈ projectiveCoverDomain p := hfull.symm ▸ mem_univ x
  exact hxvalid hx

theorem capModelEquivalence_not_isCompact_carrier
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    (U : TopologicalSpace.Opens M)
    {kind : CapModelKind} {p : RealProjectiveThree}
    (R : CapModelEquivalence kind p (U : Set M))
    (hne : (U : Set M).Nonempty) : ¬ IsCompact (U : Set M) := by
  cases hkind : kind with
  | euclidean =>
    intro hcompact
    let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
    let : TopologicalSpace R.model := R.model_topology
    let : ChartedSpace E3 R.model := R.model_charted
    let : IsManifold (𝓡 3) ∞ R.model := R.model_manifold
    obtain ⟨F, _, _⟩ := capModelEquivalence_exists_carrierDiffeomorph U R
    have hstd : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) R.model E3 ∞) := by
      have h := R.standard_smooth
      split at h
      · exact h
      · simp_all only [reduceCtorEq]
    obtain ⟨D⟩ := hstd
    let G := F.trans D
    have himage : G '' (univ : Set U) = (univ : Set E3) := by
      ext x
      constructor
      · intro _
        exact mem_univ _
      · intro _
        exact ⟨G.symm x, mem_univ _, G.apply_symm_apply x⟩
    have hE : IsCompact (univ : Set E3) := by
      rw [← himage]
      exact isCompact_univ.image G.continuous
    exact NormedSpace.unbounded_univ ℝ E3 hE.isBounded
  | puncturedProjective =>
    obtain ⟨P⟩ := capModelEquivalence_exists_puncturedProjective_cover
      U.isOpen R hkind
    exact StandardPuncturedProjectiveCover.not_isCompact_region P hne

end PoincareConjecture.M25.Topology3D
