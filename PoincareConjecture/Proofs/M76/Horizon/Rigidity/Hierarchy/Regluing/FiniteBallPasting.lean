import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.ClosedPLPasting
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Piecewise










set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

private theorem exists_continuousMap_closed_paste
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {P : Set X} (hP : IsClosed P) (old : C(X, Y)) (f : C(P, Y))
    (hboundary : ∀ x : P, (x : X) ∈ frontier P → f x = old x) :
    ∃ g : C(X, Y), (∀ x : P, g x = f x) ∧ ∀ x ∉ P, g x = old x := by
  classical
  let g (x : X) := if hx : x ∈ P then f ⟨x, hx⟩ else old x
  have hgin (x : P) : g x = f x := by simp [g, x.property]
  have hgout (x : X) (hx : x ∉ P) : g x = old x := by simp [g, hx]
  have hgc : ContinuousOn g P := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact f.continuous.congr (fun x => (hgin x).symm)
  have hgc' : Continuous (P.piecewise g old) := continuous_piecewise
    (fun x hx => (hgin ⟨x, hP.frontier_subset hx⟩).trans
      (hboundary ⟨x, hP.frontier_subset hx⟩ hx))
    (hP.closure_eq.symm ▸ hgc) old.continuous.continuousOn
  have heq : P.piecewise g old = g := by
    funext x
    by_cases hx : x ∈ P
    · simp [hx]
    · simp [hx, hgout x hx]
  exact ⟨⟨g, heq ▸ hgc'⟩, hgin, hgout⟩

local notation "V3" => (Fin 3 → ℝ)




theorem exists_finite_originalPL_relative_pasting
    {X Y ι κ η : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [Fintype η]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3}
    (old : C(X, Y))
    (hold : ChartwisePLMap e d
      (⟨fun x : (univ : Set X) => (⟨old x, mem_univ _⟩ : (univ : Set Y)),
        by fun_prop⟩ : C((univ : Set X), (univ : Set Y))))
    (P : η → Set X) (hP : ∀ i, IsClosed (P i))
    (hoverlap : ∀ i j, i ≠ j → P i ∩ P j ⊆ frontier (P i))
    (f : ∀ i, C(P i, Y))
    (hf : ∀ i, ChartwisePLMap e d
      (⟨fun x : P i => (⟨f i x, mem_univ _⟩ : (univ : Set Y)),
        by fun_prop⟩ : C(P i, (univ : Set Y))))
    (H : ∀ i, (⟨fun x : P i => old x, by fun_prop⟩ : C(P i, Y)).HomotopyRel
      (f i) ((Subtype.val : P i → X) ⁻¹' frontier (P i))) :
    ∃ g : C(X, Y),
      ChartwisePLMap e d
        (⟨fun x : (univ : Set X) => (⟨g x, mem_univ _⟩ : (univ : Set Y)),
          by fun_prop⟩ : C((univ : Set X), (univ : Set Y))) ∧
      (∀ i (x : P i), g x = f i x) ∧
      (∀ x ∉ ⋃ i, P i, g x = old x) ∧
      ∃ G : old.HomotopyRel g (⋃ i, interior (P i))ᶜ,
        ∀ i t (x : P i), G (t, (x : X)) = H i (t, x) := by
  classical
  have hex (s : Finset η) : ∃ g : C(X, Y),
      ChartwisePLMap e d
        (⟨fun x : (univ : Set X) => (⟨g x, mem_univ _⟩ : (univ : Set Y)),
          by fun_prop⟩ : C((univ : Set X), (univ : Set Y))) ∧
      ∃ G : old.HomotopyRel g (⋃ i ∈ s, interior (P i))ᶜ,
        ∀ i ∈ s, ∀ t (x : P i), G (t, (x : X)) = H i (t, x) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨old, hold, ContinuousMap.HomotopyRel.refl old _, by simp⟩
    | @insert i s his ih =>
      obtain ⟨g, hg, G, hG⟩ := ih
      have hPiFixed (x : P i) : (x : X) ∉ ⋃ j ∈ s, interior (P j) := by
        intro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        have hji : j ≠ i := fun heq => his (heq ▸ hj)
        exact disjoint_left.mp disjoint_interior_frontier hxj
          (hoverlap j i hji ⟨interior_subset hxj, x.property⟩)
      let Q : Set (unitInterval × X) := Prod.snd ⁻¹' P i
      let localH : C(Q, Y) :=
        ⟨fun z => H i (z.val.1, ⟨z.val.2, z.property⟩), by fun_prop⟩
      obtain ⟨J, hJin, hJout⟩ := exists_continuousMap_closed_paste
        ((hP i).preimage continuous_snd) G.toContinuousMap localH (by
          intro z hz
          have hx : z.val.2 ∈ frontier (P i) :=
            continuous_snd.frontier_preimage_subset (P i) hz
          exact ((H i).prop z.val.1 ⟨z.val.2, z.property⟩ hx).trans
            (G.prop z.val.1 z.val.2 (hPiFixed ⟨z.val.2, z.property⟩)).symm)
      let g' : C(X, Y) := ⟨fun x => J (1, x), by fun_prop⟩
      have hJlocal (t : unitInterval) (x : P i) : J (t, (x : X)) = H i (t, x) :=
        hJin ⟨(t, x), x.property⟩
      have hJoutside (t : unitInterval) (x : X) (hx : x ∉ P i) : J (t, x) = G (t, x) :=
        hJout (t, x) hx
      have hg'PL : ChartwisePLMap e d
          (⟨fun x : (univ : Set X) => (⟨g' x, mem_univ _⟩ : (univ : Set Y)),
            by fun_prop⟩ : C((univ : Set X), (univ : Set Y))) := by
        apply hg.closed_paste (hP i) (hf i)
        · intro x
          exact Subtype.ext ((hJlocal 1 x).trans ((H i).map_one_left x))
        · intro x hx
          exact Subtype.ext ((hJoutside 1 x hx).trans (G.map_one_left x))
      let G' : old.HomotopyRel g' (⋃ j ∈ insert i s, interior (P j))ᶜ :=
        { toContinuousMap := J
          map_zero_left := by
            intro x
            by_cases hx : x ∈ P i
            · exact (hJlocal 0 ⟨x, hx⟩).trans ((H i).map_zero_left ⟨x, hx⟩)
            · exact (hJoutside 0 x hx).trans (G.map_zero_left x)
          map_one_left := fun _ => rfl
          prop' := by
            intro t x hx
            by_cases hxi : x ∈ P i
            · apply (hJlocal t ⟨x, hxi⟩).trans
              apply (H i).prop
              exact (mem_frontier_iff_notMem_interior hxi).mpr (fun hi => hx (mem_iUnion₂.mpr
                ⟨i, Finset.mem_insert_self _ _, hi⟩))
            · apply (hJoutside t x hxi).trans
              exact G.prop t x (fun hs => hx (by
                obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hs
                exact mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩)) }
      refine ⟨g', hg'PL, G', ?_⟩
      intro j hj t x
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hJlocal t x
      · by_cases hxi : (x : X) ∈ P i
        · have hji : j ≠ i := fun heq => his (heq ▸ hj)
          exact (hJlocal t ⟨x, hxi⟩).trans
            (((H i).prop t ⟨x, hxi⟩ (hoverlap i j hji.symm ⟨hxi, x.property⟩)).trans
              ((H j).prop t x (hoverlap j i hji ⟨x.property, hxi⟩)).symm)
        · exact (hJoutside t x hxi).trans (hG j hj t x)
  obtain ⟨g, hg, G, hG⟩ := hex Finset.univ
  have hset : (⋃ i ∈ (Finset.univ : Finset η), interior (P i))ᶜ =
      (⋃ i, interior (P i))ᶜ := by simp
  let G' : old.HomotopyRel g (⋃ i, interior (P i))ᶜ :=
    { G.toHomotopy with prop' := by intro t x hx; exact G.prop t x (hset.symm ▸ hx) }
  refine ⟨g, hg, ?_, ?_, G', ?_⟩
  · intro i x
    exact (G.map_one_left x).symm.trans ((hG i (Finset.mem_univ _) 1 x).trans
      ((H i).map_one_left x))
  · intro x hx
    exact (G.map_one_left x).symm.trans (G.prop 1 x (by
      intro hi
      obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hi
      exact hx (mem_iUnion.mpr ⟨i, interior_subset hxi⟩)))
  · intro i t x
    exact hG i (Finset.mem_univ _) t x

end PoincareConjecture.M76
