import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedPairedCapTransport

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_nonnested_b1_consumer
    (S Sref Rref Rtarget : Set E3)
    (Cref Cmid Ctarget : Fin 2 → Set E3)
    (Gref Kband Fcaps Gtarget : D3)
    (Bref : BallNeighborhoodChart E3 E3)
    (hRef : Gref '' Sref = Rref ∪ Cref 0 ∪ Cref 1)
    (hK : Kband '' Rref = Rtarget)
    (hKi : Kband.symm '' Rtarget = Rref)
    (hKcap : ∀ i, Kband '' Cref i = Cmid i)
    (hKcapInv : ∀ i, Kband.symm '' Cmid i = Cref i)
    (hF : Fcaps '' (Rtarget ∪ Cmid 0 ∪ Cmid 1) =
      Rtarget ∪ Ctarget 0 ∪ Ctarget 1)
    (hFi : Fcaps.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) =
      Rtarget ∪ Cmid 0 ∪ Cmid 1)
    (hTarget : Gtarget '' S = Rtarget ∪ Ctarget 0 ∪ Ctarget 1)
    (hBref : Bref.boundary = Sref) :
    ∃ Kmid : D3, Kmid '' S = Bref.boundary := by
  obtain ⟨F, hFdef, hFimage, hFimageInv⟩ :=
    exists_nonnested_paired_cap_transport Kband Fcaps Rref Rtarget
      Cref Cmid Ctarget hK hKi hKcap hKcapInv hF hFi
  let Fref : D3 := Gref.trans F
  have hFref : Fref '' Sref = Rtarget ∪ Ctarget 0 ∪ Ctarget 1 := by
    calc
      Fref '' Sref = F '' (Gref '' Sref) := by
        change (Gref.trans F) '' Sref = _
        rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = F '' (Rref ∪ Cref 0 ∪ Cref 1) := by rw [hRef]
      _ = Rtarget ∪ Ctarget 0 ∪ Ctarget 1 := hFimage
  have hFrefInv : Fref.symm ''
      (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) = Sref := by
    rw [← hFref, image_image]
    simp only [Fref.symm_apply_apply, image_id']
  let Kmid : D3 := Gtarget.trans Fref.symm
  refine ⟨Kmid, ?_⟩
  calc
    Kmid '' S = Fref.symm '' (Gtarget '' S) := by
      change (Gtarget.trans Fref.symm) '' S = _
      rw [Diffeomorph.coe_trans, Set.image_comp]
    _ = Fref.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) := by rw [hTarget]
    _ = Sref := hFrefInv
    _ = Bref.boundary := hBref.symm

end PoincareConjecture.M25.Topology3D
