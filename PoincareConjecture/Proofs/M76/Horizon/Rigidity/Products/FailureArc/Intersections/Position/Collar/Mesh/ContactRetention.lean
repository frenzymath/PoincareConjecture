import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.EdgeMotion

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh
local notation "E" => ((ℝ × ℝ) × ℝ)

theorem normal_motion_new_contacts_active {H : E ≃ₜ E} {r c : ℝ}
    (hval : ∀ p, H p = (p.1, p.2 + c * normalMargin r p)) :
    (H '' {p : E | p.2 = 0}) \ {p : E | p.2 = 0} ⊆
      {p : E | ‖p.1‖ < r} := by
  intro p hp
  rw [normal_motion_plane_image hval] at hp
  change p.2 = c * normalMargin r (p.1, 0) ∧ p.2 ≠ 0 at hp
  change ‖p.1‖ < r
  by_contra hn
  have hle : r ≤ ‖p.1‖ := le_of_not_gt hn
  have hnorm : ‖(p.1, (0 : ℝ))‖ = ‖p.1‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg p.1)]
  have hz : normalMargin r (p.1, 0) = 0 := by
    rw [normalMargin, hnorm, max_eq_left (sub_nonpos.mpr hle)]
  apply hp.2
  rw [hp.1, hz, mul_zero]

theorem normal_motion_finite_contacts_retained {H : E ≃ₜ E} {r c : ℝ}
    (hval : ∀ p, H p = (p.1, p.2 + c * normalMargin r p)) {K W : Set E}
    (hnew : (H '' {p : E | p.2 = 0} ∩ K ∩ {p : E | ‖p.1‖ < r}).Finite)
    (hold : ({p : E | p.2 = 0} ∩ K ∩ W).Finite) :
    (H '' {p : E | p.2 = 0} ∩ K ∩ W).Finite := by
  apply (hnew.union hold).subset
  rintro p ⟨⟨hp, hpK⟩, hpW⟩
  by_cases hpold : p ∈ {p : E | p.2 = 0}
  · exact Or.inr ⟨⟨hpold, hpK⟩, hpW⟩
  · exact Or.inl ⟨⟨hp, hpK⟩, normal_motion_new_contacts_active hval ⟨hp, hpold⟩⟩

theorem exists_normal_motion_finite_contacts_retained
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (r : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c ∈ Ioo (0 : ℝ) epsilon, ∃ H : E ≃ₜ E,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ p, H p = (p.1, p.2 + c * normalMargin r p)) ∧
      EqOn H id (Metric.closedBall (0 : E) r)ᶜ ∧
      (∀ p, (H p).1 = p.1) ∧ (∀ p, (H.symm p).1 = p.1) ∧
      (H '' {p : E | p.2 = 0} ∩ K.space ∩ {p : E | ‖p.1‖ < r}).Finite ∧
      ∀ W : Set E, ({p : E | p.2 = 0} ∩ K.space ∩ W).Finite →
        (H '' {p : E | p.2 = 0} ∩ K.space ∩ W).Finite := by
  obtain ⟨c, hc, H, hPL, hval, hoff, hfst, hinv, hfinite⟩ :=
    exists_normal_motion_finite_local_edge_contacts K hK hcard r hepsilon
  exact ⟨c, hc, H, hPL, hval, hoff, hfst, hinv, hfinite,
    fun _ hW => normal_motion_finite_contacts_retained hval hfinite hW⟩

end PoincareConjecture.M76.CollarMesh
