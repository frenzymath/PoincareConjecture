import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedEndComposition

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_nonnested_bridge_of_image_chain
    (S Sref Rref Cref Rtarget Ctarget : Set E3)
    (Gref Kband Fcaps Gtarget : D3)
    (Bref : BallNeighborhoodChart E3 E3)
    (hRef : Gref '' Sref = Rref ∪ Cref)
    (hKband : Kband '' Rref = Rtarget)
    (hCaps : Fcaps '' (Rtarget ∪ Kband '' Cref) = Rtarget ∪ Ctarget)
    (hTarget : Gtarget '' S = Rtarget ∪ Ctarget)
    (hBref : Bref.boundary = Sref) :
    ∃ Kmid : D3, Kmid '' S = Bref.boundary := by
  let Fref : D3 := (Gref.trans Kband).trans Fcaps
  have hFref : Fref '' Sref = Rtarget ∪ Ctarget := by
    calc
      Fref '' Sref = Fcaps '' ((Gref.trans Kband) '' Sref) := by
        change ((Gref.trans Kband).trans Fcaps) '' Sref = _
        rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = Fcaps '' (Kband '' (Gref '' Sref)) := by
        rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = Fcaps '' (Kband '' (Rref ∪ Cref)) := by rw [hRef]
      _ = Fcaps '' (Kband '' Rref ∪ Kband '' Cref) := by
        simp only [image_union]
      _ = Fcaps '' (Rtarget ∪ Kband '' Cref) := by rw [hKband]
      _ = Rtarget ∪ Ctarget := hCaps
  have hFrefInv : Fref.symm '' (Rtarget ∪ Ctarget) = Sref := by
    rw [← hFref, image_image]
    simp only [Fref.symm_apply_apply, image_id']
  refine ⟨Gtarget.trans Fref.symm, ?_⟩
  calc
    (Gtarget.trans Fref.symm) '' S = Fref.symm '' (Gtarget '' S) := by
      rw [Diffeomorph.coe_trans, Set.image_comp]
    _ = Fref.symm '' (Rtarget ∪ Ctarget) := by rw [hTarget]
    _ = Sref := hFrefInv
    _ = Bref.boundary := hBref.symm

end PoincareConjecture.M25.Topology3D
