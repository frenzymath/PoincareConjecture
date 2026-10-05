import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IntrinsicRegularSection

/-!
# Regular polygon sections after separated cap attachment

An empty cap or a separate finite PL disk boundary preserves the
complete regular polygon union. Nonzero levels of a closed cut
also retain that union on each side. See Alexander 1924, pp. 6--8
and M76 derivation 264.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adjoining one separate simple polygon retains the actual
regular section, with no residue point. See Alexander p. 7 and
M76 derivation 264. -/
theorem HasDisjointPolygonPresentation.union_polygon
    {S : Set E} (h : HasDisjointPolygonPresentation S)
    {m : ℕ} (Q : Polygon E (m + 3)) (hQi : Function.Injective Q)
    (hQe : Q.HasSimplicialEdges) (hsep : Disjoint (Q.boundary ℝ) S) :
    HasDisjointPolygonPresentation (Q.boundary ℝ ∪ S) := by
  obtain ⟨k, n, P, hP, hcover, hpair⟩ := h
  let N : Option (Fin k) → ℕ
    | none => m
    | some i => n i
  let R : ∀ i, Polygon E (N i + 3)
    | none => Q
    | some i => P i
  have hPs (i : Fin k) : (P i).boundary ℝ ⊆ S :=
    (subset_iUnion (fun j => (P j).boundary ℝ) i).trans hcover.symm.subset
  apply hasDisjointPolygonPresentation_of_family N R
  · intro i
    cases i with
    | none => exact ⟨hQi, hQe⟩
    | some i => exact hP i
  · rw [iUnion_option, hcover]
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hsep.mono_right (hPs j)
    | some i =>
      cases j with
      | none => exact (hsep.mono_right (hPs i)).symm
      | some j => exact hpair (fun h => hij (congrArg some h))

variable [FiniteDimensional ℝ E]

/-- An empty cap or a separate finite PL disk boundary can
be adjoined without producing a residue point. The singleton
birth case is deliberately absent. See Alexander p. 7 and
M76 derivation 264. -/
theorem HasDisjointPolygonPresentation.union_regular_cap
    {S cap : Set E} (h : HasDisjointPolygonPresentation S)
    (hcap : cap = ∅ ∨ ∃ d : Set E, IsFinitePLBallPair (ℝ × ℝ) d cap)
    (hsep : Disjoint cap S) : HasDisjointPolygonPresentation (cap ∪ S) := by
  rcases hcap with rfl | ⟨d, hd⟩
  · simpa only [empty_union] using h
  · obtain ⟨m, Q, hQi, hQe, hQb⟩ := hd.exists_polygon_boundary
    rw [← hQb] at hsep ⊢
    exact h.union_polygon Q hQi hQe hsep

/-- A regular whole section has regular cut sections at any
height different from the cut plane. Closedness applies to
the actual cut carriers. See Alexander pp. 6--8 and derivation 264. -/
theorem HasDisjointPolygonPresentation.cut_level
    {S s s' : Set E} {A : E → ℝ} {c : ℝ}
    (h : HasDisjointPolygonPresentation (S ∩ {x | A x = c}))
    (hs : IsClosed s) (hs' : IsClosed s') (hA : Continuous A)
    (hunion : s ∪ s' = S) (hinter : s ∩ s' ⊆ {x | A x = 0}) (hc : c ≠ 0) :
    HasDisjointPolygonPresentation (s ∩ {x | A x = c}) ∧
      HasDisjointPolygonPresentation (s' ∩ {x | A x = c}) := by
  have hlevel : IsClosed {x | A x = c} := isClosed_eq hA continuous_const
  have hsep : Disjoint (s ∩ {x | A x = c}) (s' ∩ {x | A x = c}) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact hc (hx.2.symm.trans (hinter ⟨hx.1, hx'.1⟩))
  have hwhole : HasDisjointPolygonPresentation
      ((s ∩ {x | A x = c}) ∪ (s' ∩ {x | A x = c})) := by
    rwa [← union_inter_distrib_right, hunion]
  exact hwhole.closed_cut (hs.inter hlevel) (hs'.inter hlevel) hsep

end Set
