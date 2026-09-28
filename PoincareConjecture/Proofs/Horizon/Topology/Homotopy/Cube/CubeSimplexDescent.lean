import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeSimplexCoordinates
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

universe u

namespace Poincare.Topology

theorem exists_stdSimplex_map_of_cube_boundary {X : Type u} [TopologicalSpace X]
    (n : Nat)
    (q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))))
    (hq0 : forall t, q t 0 = ∏ k : Fin n, (1 - (t k : Real)))
    (hqs : forall t (j : Fin n), q t j.succ =
      (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1)
    (f : C((Fin n -> unitInterval), X)) (x : X)
    (hf : forall t, t ∈ Cube.boundary (Fin n) -> f t = x) :
    Exists fun g : C(stdSimplex Real (Fin (n + 1)), X) =>
      And (g.comp q = f)
        (forall z, (Exists fun j : Fin (n + 1) => z j = 0) -> g z = x) := by
  have hsurj := stdSimplex_cube_coordinates_surjective n q hq0 hqs
  have hb := stdSimplex_cube_coordinates_boundary_iff n q hq0 hqs
  have hi := stdSimplex_cube_coordinates_injOn n q hqs
  have hq := _root_.Topology.IsQuotientMap.of_surjective_continuous hsurj q.continuous
  have hfac : Function.FactorsThrough f q := by
    intro t u htu
    by_cases ht : t ∈ Cube.boundary (Fin n)
    · have hu : u ∈ Cube.boundary (Fin n) := by
        apply (hb u).mp
        rw [← htu]
        exact (hb t).mpr ht
      exact (hf t ht).trans (hf u hu).symm
    · have hu : u ∉ Cube.boundary (Fin n) := by
        intro hu
        apply ht
        apply (hb t).mp
        rw [htu]
        exact (hb u).mpr hu
      exact congrArg f (hi ht hu htu)
  let g := hq.lift f hfac
  have hg : g.comp q = f := hq.lift_comp f hfac
  refine ⟨g, hg, ?_⟩
  intro z hz
  obtain ⟨t, rfl⟩ := hsurj z
  exact (DFunLike.congr_fun hg t).trans (hf t ((hb t).mp hz))

theorem stdSimplex_cube_coordinates_homotopicRel_iff {X : Type u} [TopologicalSpace X]
    (n : Nat)
    (q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))))
    (hq0 : forall t, q t 0 = ∏ k : Fin n, (1 - (t k : Real)))
    (hqs : forall t (j : Fin n), q t j.succ =
      (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1)
    (f g : C(stdSimplex Real (Fin (n + 1)), X)) :
    ContinuousMap.HomotopicRel (f.comp q) (g.comp q) (Cube.boundary (Fin n)) <->
      ContinuousMap.HomotopicRel f g
        (Set.ofPred (fun z => Exists fun j : Fin (n + 1) => z j = 0)) := by
  have hsurj := stdSimplex_cube_coordinates_surjective n q hq0 hqs
  have hb := stdSimplex_cube_coordinates_boundary_iff n q hq0 hqs
  have hi := stdSimplex_cube_coordinates_injOn n q hqs
  let Q : C(unitInterval × (Fin n -> unitInterval),
      unitInterval × stdSimplex Real (Fin (n + 1))) :=
    ⟨fun p => (p.1, q p.2), continuous_fst.prodMk (q.continuous.comp continuous_snd)⟩
  have hQsurj : Function.Surjective Q := by
    rintro ⟨s, z⟩
    obtain ⟨t, rfl⟩ := hsurj z
    exact ⟨(s, t), rfl⟩
  have hQ := _root_.Topology.IsQuotientMap.of_surjective_continuous hQsurj Q.continuous
  constructor
  · rintro ⟨H⟩
    have hfac : Function.FactorsThrough H.toHomotopy.toContinuousMap Q := by
      rintro ⟨s, t⟩ ⟨r, u⟩ htu
      have hs : s = r := congrArg Prod.fst htu
      have htu' : q t = q u := congrArg Prod.snd htu
      subst r
      by_cases ht : t ∈ Cube.boundary (Fin n)
      · have hu : u ∈ Cube.boundary (Fin n) := by
          apply (hb u).mp
          rw [← htu']
          exact (hb t).mpr ht
        exact (H.eq_fst s ht).trans ((congrArg f htu').trans (H.eq_fst s hu).symm)
      · have hu : u ∉ Cube.boundary (Fin n) := by
          intro hu
          apply ht
          apply (hb t).mp
          rw [htu']
          exact (hb u).mpr hu
        exact congrArg (fun v => H (s, v)) (hi ht hu htu')
    let K := hQ.lift H.toHomotopy.toContinuousMap hfac
    have heq : K.comp Q = H.toHomotopy.toContinuousMap :=
      hQ.lift_comp H.toHomotopy.toContinuousMap hfac
    have heval (s : unitInterval) (t : Fin n -> unitInterval) :
        K (s, q t) = H (s, t) := DFunLike.congr_fun heq (s, t)
    refine ⟨{ toFun := K
              continuous_toFun := K.continuous
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro z
      obtain ⟨t, rfl⟩ := hsurj z
      exact (heval 0 t).trans (H.apply_zero t)
    · intro z
      obtain ⟨t, rfl⟩ := hsurj z
      exact (heval 1 t).trans (H.apply_one t)
    · intro s z hz
      obtain ⟨t, rfl⟩ := hsurj z
      exact (heval s t).trans (H.eq_fst s ((hb t).mp hz))
  · rintro ⟨K⟩
    refine ⟨{ toHomotopy := K.toHomotopy.compContinuousMap q
              prop' := ?_ }⟩
    intro s t ht
    exact K.eq_fst s ((hb t).mpr ht)

end Poincare.Topology
