import PoincareConjecture.Proofs.M59.Mathlib.CubeTransport

set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

namespace GenLoop

variable {N X : Type*} [Finite N] [DecidableEq N] [TopologicalSpace X]
  {x y : X} {p : Path x y}
  {a c : GenLoop N X x} {b d : GenLoop N X y}

namespace HomotopyAlong

def slice (H : HomotopyAlong p a b) (t : I) : GenLoop N X (p t) :=
  ⟨⟨fun v => H.toHomotopy (t, v),
    H.toHomotopy.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    fun v hv => H.boundary_path t ⟨v, hv⟩⟩

def transAt (i : N) (H : HomotopyAlong p a b) (G : HomotopyAlong p c d) :
    HomotopyAlong p (GenLoop.transAt i a c) (GenLoop.transAt i b d) where
  toFun v := GenLoop.transAt i (H.slice v.1) (G.slice v.1) v.2
  continuous_toFun := by
    change Continuous (fun v : I × (N → I) =>
      if (v.2 i : ℝ) ≤ 1 / 2 then
        H.toHomotopy (v.1, Function.update v.2 i (Set.projIcc 0 1 zero_le_one (2 * v.2 i)))
      else
        G.toHomotopy (v.1,
          Function.update v.2 i (Set.projIcc 0 1 zero_le_one (2 * v.2 i - 1))))
    refine Continuous.if_le ?_ ?_ (by fun_prop) continuous_const ?_
    · exact H.toHomotopy.continuous.comp (continuous_fst.prodMk (by fun_prop))
    · exact G.toHomotopy.continuous.comp (continuous_fst.prodMk (by fun_prop))
    · intro v hv
      have hleft : Function.update v.2 i (Set.projIcc 0 1 zero_le_one (2 * v.2 i)) ∈
          Cube.boundary N := by
        refine ⟨i, Or.inr ?_⟩
        norm_num [hv]
      have hright : Function.update v.2 i (Set.projIcc 0 1 zero_le_one (2 * v.2 i - 1)) ∈
          Cube.boundary N := by
        refine ⟨i, Or.inl ?_⟩
        norm_num [hv]
      exact (H.boundary_path v.1 ⟨_, hleft⟩).trans (G.boundary_path v.1 ⟨_, hright⟩).symm
  map_zero_left v := by
    change GenLoop.transAt i (H.slice 0) (G.slice 0) v = GenLoop.transAt i a c v
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    split_ifs
    · exact H.toHomotopy.apply_zero _
    · exact G.toHomotopy.apply_zero _
  map_one_left v := by
    change GenLoop.transAt i (H.slice 1) (G.slice 1) v = GenLoop.transAt i b d v
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    split_ifs
    · exact H.toHomotopy.apply_one _
    · exact G.toHomotopy.apply_one _
  boundary_path t v :=
    GenLoop.boundary (GenLoop.transAt i (H.slice t) (G.slice t)) v v.property

end HomotopyAlong

theorem boundaryTransport_transAt (i : N) (p : Path x y) (a b : GenLoop N X x) :
    Homotopic (boundaryTransport p (GenLoop.transAt i a b))
      (GenLoop.transAt i (boundaryTransport p a) (boundaryTransport p b)) :=
  boundaryTransport_homotopic_of_homotopyAlong
    ((boundaryTransportHomotopy p a).transAt i (boundaryTransportHomotopy p b))

end GenLoop
