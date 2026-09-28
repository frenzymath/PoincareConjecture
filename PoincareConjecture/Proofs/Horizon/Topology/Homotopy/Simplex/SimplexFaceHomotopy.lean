import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Simplex.SimplexRepresentatives
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubePrescribedNullhomotopy
import Mathlib.Topology.CompactOpen









set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace Poincare.Topology


theorem exists_stdSimplex_boundary_face_quotient (n : ℕ) :
    ∃ q : C((Σ _i : Fin (n + 2), stdSimplex ℝ (Fin (n + 1))),
      {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}),
      IsQuotientMap q ∧ ∀ i z, (q ⟨i, z⟩).val = stdSimplex.map i.succAbove z := by
  let B := {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}
  have hface (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
      stdSimplex.map i.succAbove z i = 0 := by
    have hz : stdSimplex.map i.succAbove z ∈ range (stdSimplex.map (S := ℝ) i.succAbove) :=
      mem_range_self z
    rw [stdSimplex_face_map_range] at hz
    exact hz
  let q : C((Σ _i : Fin (n + 2), stdSimplex ℝ (Fin (n + 1))), B) := {
    toFun := fun z => ⟨stdSimplex.map z.1.succAbove z.2, z.1, hface z.1 z.2⟩
    continuous_toFun := continuous_sigma fun i =>
      (stdSimplex.continuous_map i.succAbove).subtype_mk _
  }
  have hsurjective : Function.Surjective q := by
    intro y
    obtain ⟨i, hi⟩ := y.property
    have hy : y.val ∈ range (stdSimplex.map (S := ℝ) i.succAbove) := by
      rw [stdSimplex_face_map_range]
      exact hi
    obtain ⟨z, hz⟩ := hy
    exact ⟨⟨i, z⟩, Subtype.ext hz⟩
  exact ⟨q, IsQuotientMap.of_surjective_continuous hsurjective q.continuous,
    fun _ _ => rfl⟩


theorem existsUnique_stdSimplex_boundary_face_homotopy
    (n : ℕ) {X : Type*} [TopologicalSpace X]
    (q : C((Σ _i : Fin (n + 2), stdSimplex ℝ (Fin (n + 1))),
      {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}))
    (hq : IsQuotientMap q)
    (hqface : ∀ i z, (q ⟨i, z⟩).val = stdSimplex.map i.succAbove z)
    (h : Fin (n + 2) → C(unitInterval × stdSimplex ℝ (Fin (n + 1)), X))
    (hcompat : ∀ i j z w t,
      stdSimplex.map i.succAbove z = stdSimplex.map j.succAbove w →
        h i (t, z) = h j (t, w)) :
    ∃! H : C(unitInterval × {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}, X),
      ∀ t i z, H (t, q ⟨i, z⟩) = h i (t, z) := by
  let facePaths (i : Fin (n + 2)) : C(stdSimplex ℝ (Fin (n + 1)), C(unitInterval, X)) :=
    ((h i).comp ⟨Prod.swap, continuous_swap⟩).curry
  let paths : C((Σ _i : Fin (n + 2), stdSimplex ℝ (Fin (n + 1))), C(unitInterval, X)) :=
    ⟨fun z => facePaths z.1 z.2, continuous_sigma fun i => (facePaths i).continuous⟩
  have hfactors : Function.FactorsThrough paths q := by
    rintro ⟨i, z⟩ ⟨j, w⟩ heq
    ext t
    apply hcompat i j z w t
    exact (hqface i z).symm.trans ((congrArg Subtype.val heq).trans (hqface j w))
  let descended := hq.lift paths hfactors
  let H : C(unitInterval × {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}, X) :=
    descended.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  have hH (t : unitInterval) (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
      H (t, q ⟨i, z⟩) = h i (t, z) :=
    congrArg (fun a : C(unitInterval, X) => a t)
      (DFunLike.congr_fun (hq.lift_comp paths hfactors) ⟨i, z⟩)
  refine ⟨H, hH, ?_⟩
  intro K hK
  ext ⟨t, y⟩
  obtain ⟨⟨i, z⟩, rfl⟩ := hq.surjective y
  exact (hK t i z).trans (hH t i z).symm


theorem exists_stdSimplex_nullhomotopy_with_prescribed_boundary
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (hpi : Subsingleton (HomotopyGroup.Pi (n + 1) X x))
    (f : C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : C(unitInterval × {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}, X))
    (h0 : ∀ z : {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}, h (0, z) = f z)
    (h1 : ∀ z : {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}, h (1, z) = x) :
    ∃ H : f.Homotopy (ContinuousMap.const _ x),
      ∀ (t : unitInterval) (z : {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}),
        H (t, z) = h (t, z) := by
  obtain ⟨e, he⟩ := exists_stdSimplex_cube_pair_homeomorph (n + 1)
  let boundaryMap : C(Cube.boundary (Fin (n + 1)),
      {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0}) := {
    toFun := fun z => ⟨e.symm z, (he _).mpr (by
      simpa only [e.apply_symm_apply] using z.property)⟩
    continuous_toFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  }
  let cubeMap : C(I^(Fin (n + 1)), X) := f.comp ⟨e.symm, e.symm.continuous⟩
  let cubeSide : C(unitInterval × Cube.boundary (Fin (n + 1)), X) :=
    h.comp ⟨fun z => (z.1, boundaryMap z.2),
      continuous_fst.prodMk (boundaryMap.continuous.comp continuous_snd)⟩
  obtain ⟨F, hF⟩ := exists_cube_nullhomotopy_with_prescribed_boundary n x hpi cubeMap cubeSide
    (fun z => h0 (boundaryMap z)) (fun z => h1 (boundaryMap z))
  refine ⟨{
    toFun := fun z => F (z.1, e z.2)
    continuous_toFun := F.continuous.comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd))
    map_zero_left := fun z => (F.apply_zero (e z)).trans
      (congrArg f (e.symm_apply_apply z))
    map_one_left := fun z => F.apply_one (e z)
  }, fun t z => ?_⟩
  have hz : e z.val ∈ Cube.boundary (Fin (n + 1)) := (he _).mp z.property
  have hb : boundaryMap ⟨e z.val, hz⟩ = z := Subtype.ext (e.symm_apply_apply z.val)
  exact (hF t ⟨e z.val, hz⟩).trans (congrArg (fun w => h (t, w)) hb)

end Poincare.Topology
