import PoincareConjecture.Proofs.M76.Mathlib.TorusHorizontalBand

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

theorem exists_crossing_torus_band_charts {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) (hcore : 6 * d ≤ L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    let arc := ((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d
    ∃ H V : OpenPartialHomeomorph (AddCircle (4 * L) × AddCircle (4 * L)) (ℝ × ℝ),
      H.source = univ ×ˢ arc ∧ V.source = arc ×ˢ univ ∧
      EqOn H V (H.source ∩ V.source) ∧
      (∀ s ∈ Ioo (-d) d, ∀ t ∈ Ioo (-d) d,
        H ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) = (s, t)) ∧
      (∀ s ∈ Ioo (-d) d, ∀ t ∈ Ioo (-d) d,
        V ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) = (s, t)) ∧
      ∀ a b : ℝ,
        let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
          (AddCircle.openPartialHomeomorphCoe (4 * L) b)
        (Q.trans H ∈ piecewiseAffineGroupoid (ℝ × ℝ)) ∧
          Q.trans V ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  let arc := ((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d
  obtain ⟨H, hHS, _, hHcore, hHPL⟩ := exists_horizontal_torus_band hL hd hwidth hcore
  let S := (Homeomorph.prodComm (AddCircle (4 * L)) (AddCircle (4 * L))).toOpenPartialHomeomorph
  let W := (Homeomorph.prodComm ℝ ℝ).toOpenPartialHomeomorph
  let V := S.trans (H.trans W)
  have hVS : V.source = arc ×ˢ univ := by
    ext p
    change (p ∈ univ ∧ (p.2, p.1) ∈ H.source ∧ H (p.2, p.1) ∈ univ) ↔
      (p.1 ∈ arc ∧ p.2 ∈ univ)
    rw [hHS]
    simp only [mem_univ, mem_prod, true_and, and_true]
    rfl
  have hVval (p : AddCircle (4 * L) × AddCircle (4 * L)) : V p = (H p.swap).swap := rfl
  have hVcore (s : ℝ) (hs : s ∈ Ioo (-d) d) (t : ℝ) (ht : t ∈ Ioo (-d) d) :
      V ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) = (s, t) := by
    rw [hVval]
    change (H ((t : AddCircle (4 * L)), (s : AddCircle (4 * L)))).swap = (s, t)
    rw [hHcore t ht s hs]
    rfl
  have hW : W ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
    let A := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap.prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
    exact ⟨locallyPiecewiseAffineOn_affine A isOpen_univ,
      locallyPiecewiseAffineOn_affine A isOpen_univ⟩
  refine ⟨H, V, hHS, hVS, ?_, hHcore, hVcore, ?_⟩
  · intro p hp
    have hx : p.1 ∈ arc := by simpa only [hVS, mem_prod, mem_univ, and_true] using hp.2
    have hy : p.2 ∈ arc := by simpa only [hHS, mem_prod, mem_univ, true_and] using hp.1
    obtain ⟨s, hs, hsp⟩ := hx
    obtain ⟨t, ht, htp⟩ := hy
    have hpval : p = ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) :=
      Prod.ext hsp.symm htp.symm
    rw [hpval, hHcore s hs t ht, hVcore s hs t ht]
  · intro a b
    refine ⟨hHPL a b, ?_⟩
    let qa := AddCircle.openPartialHomeomorphCoe (4 * L) a
    let qb := AddCircle.openPartialHomeomorphCoe (4 * L) b
    have hswap : (qa.prod qb).trans S = W.trans (qb.prod qa) := by
      refine OpenPartialHomeomorph.ext ((qa.prod qb).trans S) (W.trans (qb.prod qa))
        (fun _ => rfl) (fun _ => rfl) ?_
      ext p
      change ((p.1 ∈ qa.source ∧ p.2 ∈ qb.source) ∧ (qa p.1, qb p.2) ∈ univ) ↔
        (p ∈ univ ∧ p.2 ∈ qb.source ∧ p.1 ∈ qa.source)
      simp only [mem_univ, true_and, and_comm]
    have hfactor : (qa.prod qb).trans V = W.trans (((qb.prod qa).trans H).trans W) := by
      calc
        (qa.prod qb).trans V = ((qa.prod qb).trans S).trans (H.trans W) :=
          (OpenPartialHomeomorph.trans_assoc _ _ _).symm
        _ = (W.trans (qb.prod qa)).trans (H.trans W) := by rw [hswap]
        _ = _ := by simp only [OpenPartialHomeomorph.trans_assoc]
    rw [hfactor]
    exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans hW
      ((piecewiseAffineGroupoid (ℝ × ℝ)).trans (hHPL b a) hW)

end PLAnnularStrip
