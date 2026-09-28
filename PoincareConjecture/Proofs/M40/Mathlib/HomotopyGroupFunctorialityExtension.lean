import PoincareConjecture.Proofs.M02.Topology.DiskHomotopyExtension
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u

namespace PoincareConjecture.Proofs.M40.Topology

noncomputable section

theorem isClosed_cube_boundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have h : Cube.boundary (Fin n) =
      ⋃ i : Fin n, {z : Fin n → unitInterval | z i = 0 ∨ z i = 1} := by
    ext z
    simp [Cube.boundary]
  rw [h]
  apply isClosed_iUnion_of_finite
  intro i
  exact (isClosed_eq (continuous_apply i) continuous_const).union
    (isClosed_eq (continuous_apply i) continuous_const)

theorem continuous_cube_cons (n : ℕ) :
    Continuous (fun p : unitInterval × (Fin n → unitInterval) =>
      (Fin.cons p.1 p.2 : Fin (n + 1) → unitInterval)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

theorem exists_cube_boundary_homotopy_extension
    {Y : Type u} [TopologicalSpace Y] (n : ℕ)
    (f : C((Fin n → unitInterval), Y))
    (H : C(unitInterval × Cube.boundary (Fin n), Y))
    (h0 : ∀ z : Cube.boundary (Fin n), H (0, z) = f z.val) :
    ∃ F : C(unitInterval × (Fin n → unitInterval), Y),
      (∀ z, F (0, z) = f z) ∧
      (∀ (t : unitInterval) (z : Cube.boundary (Fin n)), F (t, z.val) = H (t, z)) := by
  obtain ⟨e, he⟩ := M02.Topology.exists_cube_ball_coordinates n
  let b : C(sphere (0 : Fin n → ℝ) 1, Cube.boundary (Fin n)) :=
    ⟨fun z => ⟨e.symm ⟨z.val, sphere_subset_closedBall z.property⟩, by
      apply (he _).mpr
      rw [e.apply_symm_apply]
      exact mem_sphere_zero_iff_norm.mp z.property⟩, by fun_prop⟩
  let f' := f.comp ⟨e.symm, e.symm.continuous⟩
  let H' : C(unitInterval × sphere (0 : Fin n → ℝ) 1, Y) :=
    H.comp ⟨fun p => (p.1, b p.2), by fun_prop⟩
  obtain ⟨F, hF0, hFs⟩ := M02.Topology.exists_disk_homotopy_extension f' H'
    (fun z => h0 (b z))
  refine ⟨F.comp ⟨fun p => (p.1, e p.2), by fun_prop⟩, ?_, ?_⟩
  · intro z
    exact (hF0 (e z)).trans (congrArg f (e.symm_apply_apply z))
  · intro t z
    let s : sphere (0 : Fin n → ℝ) 1 :=
      ⟨(e z.val).val, mem_sphere_zero_iff_norm.mpr ((he z.val).mp z.property)⟩
    have hb : b s = z := Subtype.ext (e.symm_apply_apply z.val)
    exact (hFs t s).trans (congrArg H (Prod.ext rfl hb))

theorem homotopicRel_of_nullhomotopic_boundary_trace
    {Y : Type u} [TopologicalSpace Y] {n : ℕ} {y : Y}
    (a b : GenLoop (Fin n) Y y) (H : a.val.Homotopy b.val)
    (p : Path y y) (hp : ∀ (t : unitInterval) (z : Cube.boundary (Fin n)),
      H (t, z.val) = p t) (J : p.Homotopy (Path.refl y)) :
    GenLoop.Homotopic a b := by
  classical
  let tail (z : Fin (n + 1) → unitInterval) : Fin n → unitInterval := fun i => z i.succ
  have htcont : Continuous tail := continuous_pi fun i => continuous_apply i.succ
  let B (q : unitInterval × Cube.boundary (Fin (n + 1))) : Y :=
    if q.2.val 0 = 0 then a (tail q.2.val)
    else if q.2.val 0 = 1 then b (tail q.2.val)
    else J (q.1, q.2.val 0)
  let A0 : Set (unitInterval × Cube.boundary (Fin (n + 1))) := {q | q.2.val 0 = 0}
  let A1 : Set (unitInterval × Cube.boundary (Fin (n + 1))) := {q | q.2.val 0 = 1}
  let As : Set (unitInterval × Cube.boundary (Fin (n + 1))) :=
    {q | tail q.2.val ∈ Cube.boundary (Fin n)}
  have htime : Continuous (fun q : unitInterval × Cube.boundary (Fin (n + 1)) =>
      q.2.val 0) := (continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd)
  have hA0 : IsClosed A0 := isClosed_eq htime continuous_const
  have hA1 : IsClosed A1 := isClosed_eq htime continuous_const
  have hAs : IsClosed As := (isClosed_cube_boundary n).preimage
    (htcont.comp (continuous_subtype_val.comp continuous_snd))
  have hcover : A0 ∪ (A1 ∪ As) = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := q.2.property
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · intro h
      exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact Or.inr (Or.inr ⟨j, hj⟩)
  have hcont : Continuous B := by
    rw [← continuousOn_univ, ← hcover]
    apply (continuousOn_union_iff_of_isClosed hA0 (hA1.union hAs)).mpr
    constructor
    · apply (a.val.continuous.comp
        (htcont.comp (continuous_subtype_val.comp continuous_snd))).continuousOn.congr
      intro q hq
      simp [B, show q.2.val 0 = 0 from hq]
    · apply (continuousOn_union_iff_of_isClosed hA1 hAs).mpr
      constructor
      · apply (b.val.continuous.comp
          (htcont.comp (continuous_subtype_val.comp continuous_snd))).continuousOn.congr
        intro q hq
        simp [B, show q.2.val 0 = 1 from hq]
      · apply (J.continuous.comp (continuous_fst.prodMk htime)).continuousOn.congr
        intro q hq
        change B q = J (q.1, q.2.val 0)
        dsimp only [B]
        split_ifs with h0 h1
        · rw [h0, J.source]
          exact a.property _ hq
        · rw [h1, J.target]
          exact b.property _ hq
        · rfl
  let H' : C((Fin (n + 1) → unitInterval), Y) :=
    H.toContinuousMap.comp ⟨fun z => (z 0, tail z), (continuous_apply 0).prodMk htcont⟩
  have hB0 (z : Cube.boundary (Fin (n + 1))) : B (0, z) = H' z.val := by
    dsimp only [B, H', ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    split_ifs with h0 h1
    · rw [h0]
      exact (H.apply_zero (tail z.val)).symm
    · rw [h1]
      exact (H.apply_one (tail z.val)).symm
    · rw [J.apply_zero]
      apply (hp (z.val 0) ⟨tail z.val, ?_⟩).symm
      obtain ⟨i, hi⟩ := z.property
      refine Fin.cases ?_ (fun j hj => ⟨j, hj⟩) i hi
      exact fun h => (h.elim h0 h1).elim
  obtain ⟨F, _, hFs⟩ := exists_cube_boundary_homotopy_extension (n + 1) H' ⟨B, hcont⟩ hB0
  refine ⟨{ toFun := fun q => F (1, Fin.cons q.1 q.2)
            continuous_toFun := F.continuous.comp
              (continuous_const.prodMk (continuous_cube_cons n))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro z
    have h := hFs 1 ⟨Fin.cons 0 z, ⟨0, Or.inl rfl⟩⟩
    simpa [B, tail] using h
  · intro z
    have h := hFs 1 ⟨Fin.cons 1 z, ⟨0, Or.inr rfl⟩⟩
    simpa [B, tail] using h
  · intro t z hz
    have hz' : Fin.cons t z ∈ Cube.boundary (Fin (n + 1)) := by
      obtain ⟨i, hi⟩ := hz
      exact ⟨i.succ, hi⟩
    have h := hFs 1 ⟨Fin.cons t z, hz'⟩
    change F (1, Fin.cons t z) = a z
    rw [h]
    change (if t = 0 then a z else if t = 1 then b z else J (1, t)) = a z
    split_ifs
    · rfl
    · exact (b.property z hz).trans (a.property z hz).symm
    · exact (J.apply_one t).trans (a.property z hz).symm

theorem homotopicRel_of_uniform_boundary_trace
    {Y : Type u} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    {n : ℕ} {y : Y} (a b : GenLoop (Fin n) Y y)
    (H : a.val.Homotopy b.val) (p : Path y y)
    (hp : ∀ (t : unitInterval) (z : Cube.boundary (Fin n)), H (t, z.val) = p t) :
    GenLoop.Homotopic a b := by
  obtain ⟨J⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl y)
  exact homotopicRel_of_nullhomotopic_boundary_trace a b H p hp J

end

end PoincareConjecture.Proofs.M40.Topology
