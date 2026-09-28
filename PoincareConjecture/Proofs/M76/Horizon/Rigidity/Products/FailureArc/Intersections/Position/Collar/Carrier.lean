import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.LineNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FinitePLSignedSides
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_finite_boundary_intersection_collar
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hG : G.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : Set X) (rim : Set E) (hrim : IsCompact rim) (hrimK : rim ⊆ K.space)
    (hGs : G.space = {z | z ∈ K.space ∧ g z ∈ S})
    (hboundary : ∀ x ∈ G.space ∩ rim,
      Nonempty (OriginalSurfacePairChart e S (g '' K.space) (g x) true))
    {z : E → ℝ} (hz : FinitePiecewiseAffineOn z K.space)
    (hznonneg : ∀ x ∈ K.space, 0 ≤ z x)
    (hzzero : ∀ x ∈ K.space, z x = 0 ↔ x ∈ rim)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (ε : ℝ) (M H : SimplicialComplex ℝ E),
      0 < ε ∧ ε < δ ∧ M.faces.Finite ∧ H.faces.Finite ∧
      M.space = K.space ∩ {x | z x ≤ ε} ∧
      H.space = G.space ∩ M.space ∧
      rim ⊆ M.space ∧
      (∀ a ∈ H.faces, a.card ≤ 2) ∧
      FinitePiecewiseAffineOn z H.space ∧
      ∃ lines : Finset (AffineSubspace ℝ E),
        (∀ A ∈ lines, Module.finrank ℝ A.direction ≤ 1) ∧
        ∀ x ∈ H.space, ∃ A ∈ lines, x ∈ A := by
  obtain ⟨U, lines, hU, hrimU, hdim, hline⟩ :=
    exists_boundary_intersection_line_neighborhood K G hK hG hg hgi S rim hrim hGs hboundary
  have hcompact := (K.isCompact_space_of_finite hK).diff hU
  obtain ⟨b, hb, hbound⟩ := hcompact.exists_forall_le'
    (hz.continuousOn.mono sdiff_subset) (by
      intro x hx
      exact lt_of_le_of_ne (hznonneg x hx.1)
        (fun h => hx.2 (hrimU ((hzzero x hx.1).mp h.symm))))
  let ε := min b δ / 2
  have hε : 0 < ε := half_pos (lt_min hb hδ)
  have hεb : ε < b := (half_lt_self (lt_min hb hδ)).trans_le (min_le_left b δ)
  have hεδ : ε < δ := (half_lt_self (lt_min hb hδ)).trans_le (min_le_right b δ)
  obtain ⟨M, hM, hMs⟩ := hz.exists_finite_sublevel_complex ε
  obtain ⟨H, hH, hHs⟩ := G.exists_finite_triangulation_inter M hG hM
  have hMU : M.space ⊆ U := by
    intro x hx
    by_contra hn
    obtain ⟨hxK, hxε⟩ := hMs.subset hx
    exact (hεb.trans_le (hbound x ⟨hxK, hn⟩)).not_ge hxε
  have hMK : M.space ⊆ K.space := hMs.subset.trans inter_subset_left
  refine ⟨ε, M, H, hε, hεδ, hM, hH, hMs, hHs, ?_, ?_,
    hz.restrict H hH (hHs.subset.trans (inter_subset_right.trans hMK)),
    lines, hdim, fun x hx => hline x ⟨(hHs.subset hx).1, hMU (hHs.subset hx).2⟩⟩
  · intro x hx
    exact hMs.symm.subset ⟨hrimK hx, by
      change z x ≤ ε
      rw [(hzzero x (hrimK hx)).mpr hx]
      exact hε.le⟩
  · intro a ha
    apply H.face_card_le_of_finite_affine_cover lines hdim (fun x hx => ?_) ha
    exact hline x ⟨(hHs.subset hx).1, hMU (hHs.subset hx).2⟩

end PoincareConjecture.M76
