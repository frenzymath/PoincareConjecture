import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusRegion










set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

local notation "P2" => (ℝ × ℝ)




theorem exists_oriented_polygon_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E ≃L[ℝ] P2) {T : Set E} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL) :
    ∃ (m n : ℕ) (P : Polygon E (m + 3)) (I : Polygon E (n + 3)) (reverse : Bool),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
      I.HasSimplicialEdges ∧ Function.Injective I ∧
      closure I.inside ⊆ P.inside ∧ T = closure P.inside \ I.inside ∧
      ∃ (r : squareAnnulus L d ≃ₜ squareAnnulus L d)
        (b : squareAnnulus L d ≃ₜ ↥(closure P.inside \ I.inside)),
        r.IsFinitePL ∧ b.IsFinitePL ∧ b.symm.IsFinitePL ∧
        (∀ p, (b p : E) = c (r p)) ∧
        (∀ p, depth L (r p) = if reverse then -depth L p else depth L p) ∧
        (∀ p, (b p : E) ∈ P.boundary ℝ ↔ depth L p = -d) ∧
        (∀ p, (b p : E) ∈ I.boundary ℝ ↔ depth L p = d) ∧
        ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
          (r ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
            annulus_period_point_mem hd hwidth _ u⟩ : P2) =
            annulusMap L (by linarith)
              ((s : AddCircle (4 * L)), if reverse then -(u : ℝ) else u) := by
  obtain ⟨m, n, P, I, reverse, hP, hPi, hI, hIi, hnest, hregion,
    hout, hin, b, hb, _, hbc⟩ :=
    exists_polygon_collar_of_square_annulus_in_plane a hd hwidth c hc
  refine ⟨m, n, P, I, reverse, hP, hPi, hI, hIi, hnest, hregion, ?_⟩
  cases reverse
  · obtain ⟨K, hK, hKs⟩ := exists_finite_square_annulus_complex hd hwidth
    have hr : (Homeomorph.refl (squareAnnulus L d)).IsFinitePL :=
      ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ P2)⟩,
        fun _ ↦ rfl⟩
    exact ⟨Homeomorph.refl _, b, hr, hb, hb.symm, hbc, fun _ ↦ rfl,
      fun p ↦ by rw [hbc]; exact hout p,
      fun p ↦ by rw [hbc]; exact hin p, fun _ _ _ ↦ rfl⟩
  · obtain ⟨r, hr, hrdepth, hrperiod⟩ := exists_square_annulus_depth_reflection hd hwidth
    refine ⟨r, r.trans b, hr, hr.trans hb, (hr.trans hb).symm,
      fun p ↦ hbc (r p), hrdepth, ?_, ?_, hrperiod⟩
    · intro p
      change (b (r p) : E) ∈ P.boundary ℝ ↔ _
      rw [hbc, hout, hrdepth]
      exact neg_eq_iff_eq_neg
    · intro p
      change (b (r p) : E) ∈ I.boundary ℝ ↔ _
      rw [hbc, hin, hrdepth]
      exact neg_inj

end Dehn
