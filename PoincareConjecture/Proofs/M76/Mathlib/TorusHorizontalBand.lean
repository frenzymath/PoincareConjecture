import PoincareConjecture.Proofs.M76.Mathlib.CenteredAnnulusChart
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

theorem exists_horizontal_torus_band {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) (hcore : 6 * d ≤ L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    ∃ H : OpenPartialHomeomorph (AddCircle (4 * L) × AddCircle (4 * L)) (ℝ × ℝ),
      H.source = univ ×ˢ (((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d) ∧
      (∀ p, H p = centeredAnnulusMap L hL
        (p.1, (AddCircle.shortArcQuotient (4 * L) d).symm p.2)) ∧
      (∀ s ∈ Ioo (-d) d, ∀ t ∈ Ioo (-d) d,
        H ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) = (s, t)) ∧
      ∀ a b : ℝ, ((AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
        (AddCircle.openPartialHomeomorphCoe (4 * L) b)).trans H ∈
          piecewiseAffineGroupoid (ℝ × ℝ) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hdhalf : d < (4 * L) / 2 := by linarith
  obtain ⟨e, heS, heval, hePL⟩ := exists_centeredAnnulus_PL_openPartialHomeomorph hL hd hwidth
  let q := AddCircle.shortArcQuotient (4 * L) d
  let H := ((OpenPartialHomeomorph.refl (AddCircle (4 * L))).prod q.symm).trans e
  have hHS : H.source = univ ×ˢ q.target := by
    ext p
    change ((p.1 ∈ univ ∧ p.2 ∈ q.target) ∧ (p.1, q.symm p.2) ∈ e.source) ↔
      (p.1 ∈ univ ∧ p.2 ∈ q.target)
    constructor
    · exact And.left
    · intro hp
      refine ⟨hp, ?_⟩
      rw [heS]
      refine ⟨mem_univ _, ?_⟩
      rw [← AddCircle.shortArcQuotient_source (4 * L) hdhalf]
      exact q.symm.mapsTo hp.2
  have hHval (p : AddCircle (4 * L) × AddCircle (4 * L)) :
      H p = centeredAnnulusMap L hL (p.1, q.symm p.2) := by
    change e (p.1, q.symm p.2) = _
    rw [heval]
  refine ⟨H, ?_, hHval, ?_, ?_⟩
  · rw [hHS, AddCircle.shortArcQuotient_target (4 * L) hdhalf]
  · intro s hs t ht
    rw [hHval, AddCircle.shortArcQuotient_symm_coe (4 * L) hdhalf ht]
    exact centeredAnnulusMap_core hL hwidth hcore
      (abs_le.mpr ⟨hs.1.le, hs.2.le⟩) (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  · intro a b
    let qa := AddCircle.openPartialHomeomorphCoe (4 * L) a
    let qb := AddCircle.openPartialHomeomorphCoe (4 * L) b
    have hfactor : (qa.prod qb).trans H =
        ((OpenPartialHomeomorph.refl ℝ).prod (qb.trans q.symm)).trans
          ((qa.prod (OpenPartialHomeomorph.refl ℝ)).trans e) := by
      simp only [H, ← OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.prod_trans,
        OpenPartialHomeomorph.trans_refl, OpenPartialHomeomorph.refl_trans]
    rw [hfactor]
    apply (piecewiseAffineGroupoid (ℝ × ℝ)).trans
    · exact piecewiseAffineGroupoid_prod _ _ (piecewiseAffineGroupoid ℝ).id_mem
        (AddCircle.shortArcQuotient_transition_mem_piecewiseAffineGroupoid (4 * L) d b)
    · exact hePL a

end PLAnnularStrip
