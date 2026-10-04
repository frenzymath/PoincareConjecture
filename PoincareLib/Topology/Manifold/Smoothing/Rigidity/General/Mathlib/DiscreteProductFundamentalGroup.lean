import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Fundamental groups of products with a disconnected factor

Every path in a totally disconnected factor is constant. A homotopy
of the second-coordinate loops therefore lifts with the fixed first
coordinate. This proves the boundary-group injection used in
Waldhausen 1968, Theorem 6.1, p. 77, for interval-torus handles.
-/

set_option autoImplicit false

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TotallyDisconnectedSpace X]

/-- The second projection induces an injection on based groups when
the first factor is totally disconnected, without connectedness of the
whole product or a global section through every component at once. -/
theorem map_snd_injective_of_totallyDisconnected (x : X × Y) :
    Function.Injective (map (⟨Prod.snd, continuous_snd⟩ : C(X × Y, Y)) x) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
  have hfst (p : Path x x) (t : unitInterval) : (p t).1 = x.1 := by
    have h := TotallyDisconnectedSpace.eq_of_continuous (fun s => (p s).1)
      (continuous_fst.comp p.continuous) t 0
    exact h.trans (congrArg Prod.fst p.source)
  obtain ⟨H⟩ : (a.map continuous_snd).Homotopic (b.map continuous_snd) :=
    Path.Homotopic.Quotient.exact hab
  apply Path.Homotopic.Quotient.eq.mpr
  refine ⟨{
    toFun := fun z => (x.1, H z)
    continuous_toFun := continuous_const.prodMk H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact Prod.ext (hfst a t).symm (H.apply_zero t)
  · intro t
    exact Prod.ext (hfst b t).symm (H.apply_one t)
  · intro t s hs
    exact Prod.ext (hfst a s).symm (H.eq_fst t hs)

end FundamentalGroup
