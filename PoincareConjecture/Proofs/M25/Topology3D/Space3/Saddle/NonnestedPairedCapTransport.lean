import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedBridgeImageChain

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_nonnested_paired_cap_transport
    (Kband Fcaps : D3)
    (Rref Rtarget : Set E3)
    (Cref Cmid Ctarget : Fin 2 → Set E3)
    (hK : Kband '' Rref = Rtarget)
    (hKi : Kband.symm '' Rtarget = Rref)
    (hKcap : ∀ i, Kband '' Cref i = Cmid i)
    (hKcapInv : ∀ i, Kband.symm '' Cmid i = Cref i)
    (hF : Fcaps '' (Rtarget ∪ Cmid 0 ∪ Cmid 1) =
      Rtarget ∪ Ctarget 0 ∪ Ctarget 1)
    (hFi : Fcaps.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) =
      Rtarget ∪ Cmid 0 ∪ Cmid 1) :
    ∃ F : D3,
      F = Kband.trans Fcaps ∧
      F '' (Rref ∪ Cref 0 ∪ Cref 1) =
        Rtarget ∪ Ctarget 0 ∪ Ctarget 1 ∧
      F.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) =
        Rref ∪ Cref 0 ∪ Cref 1 := by
  let F : D3 := Kband.trans Fcaps
  have hinner : Kband '' (Rref ∪ Cref 0 ∪ Cref 1) =
      Rtarget ∪ Cmid 0 ∪ Cmid 1 := by
    rw [image_union, image_union, hK, hKcap 0, hKcap 1]
  have hinnerInv : Kband.symm '' (Rtarget ∪ Cmid 0 ∪ Cmid 1) =
      Rref ∪ Cref 0 ∪ Cref 1 := by
    rw [image_union, image_union, hKi, hKcapInv 0, hKcapInv 1]
  have hFforward : F '' (Rref ∪ Cref 0 ∪ Cref 1) =
      Rtarget ∪ Ctarget 0 ∪ Ctarget 1 := by
    calc
      F '' (Rref ∪ Cref 0 ∪ Cref 1) =
          Fcaps '' (Kband '' (Rref ∪ Cref 0 ∪ Cref 1)) := by
            change (Kband.trans Fcaps) '' (Rref ∪ Cref 0 ∪ Cref 1) = _
            rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = Fcaps '' (Rtarget ∪ Cmid 0 ∪ Cmid 1) := by
            rw [hinner]
      _ = Rtarget ∪ Ctarget 0 ∪ Ctarget 1 := hF
  have hFinverse : F.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) =
      Rref ∪ Cref 0 ∪ Cref 1 := by
    calc
      F.symm '' (Rtarget ∪ Ctarget 0 ∪ Ctarget 1) =
          Kband.symm '' (Fcaps.symm ''
            (Rtarget ∪ Ctarget 0 ∪ Ctarget 1)) := by
            change (Kband.trans Fcaps).symm '' _ = _
            rw [Diffeomorph.symm_trans', Diffeomorph.coe_trans,
              Set.image_comp]
      _ = Kband.symm '' (Rtarget ∪ Cmid 0 ∪ Cmid 1) := by rw [hFi]
      _ = Rref ∪ Cref 0 ∪ Cref 1 := by
            rw [hinnerInv]
  exact ⟨F, rfl, hFforward, hFinverse⟩

end PoincareConjecture.M25.Topology3D
