import PoincareConjecture.Proofs.M59.Mathlib.CubicalAdjunction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

set_option autoImplicit false

open scoped Topology unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem homotopic_trans_trace (p q : Path x x)
    (H : p.toContinuousMap.Homotopy q.toContinuousMap)
    (htrace : ∀ t, H (t, 0) = H (t, 1)) :
    ∃ r : Path x x, (p.trans r).Homotopic (r.trans q) := by
  let r : Path x x := (H.evalAt 0).cast p.source.symm q.source.symm
  obtain ⟨K⟩ := Path.Homotopic.map_trans_evalAt H Path.id
  refine ⟨r, ⟨(K.pathCast p.source.symm q.target.symm).cast ?_ ?_⟩⟩
  · ext t
    simp only [Path.cast_coe, Path.trans_apply]
    split_ifs
    · rfl
    · exact (htrace _).symm
  · ext t
    simp only [Path.cast_coe, Path.trans_apply]
    split_ifs <;> rfl

theorem homotopic_of_free_homotopy
    (hcomm : ∀ a b : FundamentalGroup X x, a * b = b * a)
    (p q : Path x x) (H : p.toContinuousMap.Homotopy q.toContinuousMap)
    (htrace : ∀ t, H (t, 0) = H (t, 1)) : p.Homotopic q := by
  obtain ⟨r, h⟩ := homotopic_trans_trace p q H htrace
  let P : FundamentalGroup X x := Homotopic.Quotient.mk p
  let Q : FundamentalGroup X x := Homotopic.Quotient.mk q
  let R : FundamentalGroup X x := Homotopic.Quotient.mk r
  have he : R * P = Q * R := by
    change Homotopic.Quotient.mk (p.trans r) = Homotopic.Quotient.mk (r.trans q)
    exact Quotient.sound h
  rw [hcomm Q R] at he
  have hPQ : P = Q := mul_left_cancel he
  exact Quotient.exact hPQ

end Path
