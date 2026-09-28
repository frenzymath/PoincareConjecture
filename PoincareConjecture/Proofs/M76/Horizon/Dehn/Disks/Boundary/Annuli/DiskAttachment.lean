import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]



theorem isFinitePLBallPair_attach_annulus_inner {D A q r : Set E} {L d : ℝ}
    (hD : IsFinitePLBallPair P2 D q) (hcontact : D ∩ A = q)
    (hd : 0 < d) (hwidth : 2 * d < L)
    (c : squareAnnulus L d ≃ₜ A) (hc : c.IsFinitePL)
    (hinner : ∀ z : squareAnnulus L d, depth L z = d ↔ (c z : E) ∈ q)
    (hrA : r ⊆ A)
    (houter : ∀ z : squareAnnulus L d, depth L z = -d ↔ (c z : E) ∈ r) :
    IsFinitePLBallPair P2 (D ∪ A) r := by
  obtain ⟨hpartition, hinter, hrim⟩ := Dehn.annulusSquare_partition (L := L) hd
  have hs : IsFinitePLBallPair P2
      (Dehn.annulusSquare L d ∪ squareAnnulus L d)
      (frontier (Dehn.annulusSquare L (-d))) :=
    hpartition.symm ▸ Dehn.isFinitePLBallPair_annulusSquare (show 2 * (-d) < L by linarith)
  have ha := Dehn.isFinitePLBallPair_annulusSquare hwidth
  have hmem (z : squareAnnulus L d) :
      (z : P2) ∈ frontier (Dehn.annulusSquare L d) ↔ (c z : E) ∈ q :=
    (Dehn.mem_frontier_annulusSquare_iff L d z).trans (hinner z)
  obtain ⟨f, hfPL, hf⟩ := hc
  have hboundary : f '' frontier (Dehn.annulusSquare L (-d)) = r := by
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      rw [← hf ⟨w, hrim hw⟩]
      exact (houter ⟨w, hrim hw⟩).mp
        ((Dehn.mem_frontier_annulusSquare_iff L (-d) w).mp hw)
    · intro z hz
      let w := c.symm ⟨z, hrA hz⟩
      have hw : (w : P2) ∈ frontier (Dehn.annulusSquare L (-d)) := by
        apply (Dehn.mem_frontier_annulusSquare_iff L (-d) w).mpr
        apply (houter w).mpr
        simpa only [w, Homeomorph.apply_symm_apply] using hz
      refine ⟨w, hw, ?_⟩
      rw [← hf w]
      exact congrArg Subtype.val (c.apply_symm_apply ⟨z, hrA hz⟩)
  obtain ⟨hball, _⟩ := hs.exists_piece_replacement ha hD hinter hcontact hrim c
    ⟨f, hfPL, hf⟩ hmem hf
  exact hboundary ▸ hball



theorem isFinitePLBallPair_attach_annulus_outer {D A q r : Set E} {L d : ℝ}
    (hD : IsFinitePLBallPair P2 D q) (hcontact : D ∩ A = q)
    (hd : 0 < d) (hwidth : 4 * d < L)
    (c : squareAnnulus L d ≃ₜ A) (hc : c.IsFinitePL)
    (houter : ∀ z : squareAnnulus L d, depth L z = -d ↔ (c z : E) ∈ q)
    (hrA : r ⊆ A)
    (hinner : ∀ z : squareAnnulus L d, depth L z = d ↔ (c z : E) ∈ r) :
    IsFinitePLBallPair P2 (D ∪ A) r := by
  obtain ⟨s, hs, hdepth, _⟩ := Dehn.exists_square_annulus_depth_reflection hd hwidth
  apply isFinitePLBallPair_attach_annulus_inner hD hcontact hd (by linarith)
    (s.trans c) (hs.trans hc) ?_ hrA ?_
  · intro z
    have h := houter (s z)
    rw [hdepth] at h
    simpa only [Homeomorph.trans_apply, neg_inj] using h
  · intro z
    have h := hinner (s z)
    rw [hdepth] at h
    exact (show depth L z = -d ↔ -depth L z = d by constructor <;> intro h <;> linarith).trans h

end PoincareConjecture.M76.Dehn
