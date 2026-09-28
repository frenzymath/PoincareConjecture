import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedB1Consumer













set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞





theorem exists_nonnested_b1_consumer_of_root_paired_alignment
    (S Sref Rref Rtarget : Set E3)
    (Cref Cmid Ctarget : Fin 2 → Set E3)
    (Gref Kband Falign Gtarget : D3)
    (Bref : BallNeighborhoodChart E3 E3)
    (hRef : Gref '' Sref = Rref ∪ Cref 0 ∪ Cref 1)
    (hK : Kband '' Rref = Rtarget)
    (hKi : Kband.symm '' Rtarget = Rref)
    (hKcap : ∀ i, Kband '' Cref i = Cmid i)
    (hKcapInv : ∀ i, Kband.symm '' Cmid i = Cref i)
    (_hAlignCap : ∀ i,
      Falign '' Cmid i = Ctarget i ∧
      Falign.symm '' Ctarget i = Cmid i)
    (hAlign : Falign '' (Rtarget ∪ Cmid 0 ∪ Cmid 1) =
      Rtarget ∪ Ctarget 0 ∪ Ctarget 1)
    (hAlignInv : Falign.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) =
      Rtarget ∪ Cmid 0 ∪ Cmid 1)
    (hTarget : Gtarget '' S = Rtarget ∪ Ctarget 0 ∪ Ctarget 1)
    (hBref : Bref.boundary = Sref) :
    ∃ Kmid : D3, Kmid '' S = Bref.boundary := by
  exact exists_nonnested_b1_consumer S Sref Rref Rtarget Cref Cmid Ctarget
    Gref Kband Falign Gtarget Bref hRef hK hKi hKcap hKcapInv hAlign hAlignInv
    hTarget hBref

end PoincareConjecture.M25.Topology3D
