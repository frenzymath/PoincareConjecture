import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.ComponentLoopReflection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.WhiskeredLoopSplit

set_option autoImplicit false

namespace Path

variable {X : Type*} [TopologicalSpace X] {b v : X}

theorem whiskeredLoopClass_eq_one_iff (p : Path b v) (q : Path v v) :
    p.whiskeredLoopClass q = 1 ↔
      FundamentalGroup.fromPath (Homotopic.Quotient.mk q) = 1 := by
  constructor
  · intro h
    change ((Homotopic.Quotient.mk p).trans (Homotopic.Quotient.mk q)).trans
      (Homotopic.Quotient.mk p).symm = Homotopic.Quotient.refl b at h
    have hh := congrArg (fun r : Homotopic.Quotient b b =>
      ((Homotopic.Quotient.mk p).symm.trans r).trans (Homotopic.Quotient.mk p)) h
    simp only [Homotopic.Quotient.trans_assoc, Homotopic.Quotient.symm_trans,
      Homotopic.Quotient.trans_refl] at hh
    rw [← Homotopic.Quotient.trans_assoc, Homotopic.Quotient.symm_trans,
      Homotopic.Quotient.refl_trans] at hh
    exact hh
  · intro h
    change ((Homotopic.Quotient.mk p).trans (Homotopic.Quotient.mk q)).trans
      (Homotopic.Quotient.mk p).symm = Homotopic.Quotient.refl b
    change Homotopic.Quotient.mk q = Homotopic.Quotient.refl v at h
    rw [h, Homotopic.Quotient.trans_refl, Homotopic.Quotient.trans_symm]

end Path

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem loopClass_map_eq_one_iff (H : X ≃ₜ Y) {x : X} (q : Path x x) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (q.map H.continuous)) = 1 ↔
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) = 1 := by
  have hrefl : (Path.refl x).map H.continuous = Path.refl (H x) := by
    ext t
    rfl
  constructor
  · intro h
    have hhom : (q.map H.continuous).Homotopic (Path.refl (H x)) :=
      Path.Homotopic.Quotient.exact h
    have hhom' : (q.map H.continuous).Homotopic ((Path.refl x).map H.continuous) := by
      simpa only [hrefl] using hhom
    exact Path.Homotopic.Quotient.eq.mpr (hhom'.of_map_homeomorph H)
  · intro h
    have hhom : q.Homotopic (Path.refl x) := Path.Homotopic.Quotient.exact h
    have hmapped := hhom.map ⟨H, H.continuous⟩
    change Path.Homotopic.Quotient.mk (q.map H.continuous) =
      Path.Homotopic.Quotient.mk (Path.refl (H x))
    simpa only [hrefl] using Path.Homotopic.Quotient.eq.mpr hmapped

end Homeomorph
