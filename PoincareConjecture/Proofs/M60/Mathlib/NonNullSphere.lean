import PoincareConjecture.Proofs.M02.CubeSphere
import PoincareConjecture.Proofs.M40.Mathlib.HomotopyGroupFunctorialityExtension











set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

namespace PoincareConjecture.M60





theorem genLoop_homotopic_const_of_uniform_nullhomotopy
    {Y : Type*} [TopologicalSpace Y] {n : ℕ} {y z : Y}
    (a : GenLoop (Fin n) Y y)
    (H : a.val.Homotopy (ContinuousMap.const _ z)) (p : Path y z)
    (hp : ∀ (t : unitInterval) (q : Cube.boundary (Fin n)), H (t, q.val) = p t) :
    GenLoop.Homotopic a GenLoop.const := by
  let K : (ContinuousMap.const (Fin n → unitInterval) z).Homotopy
      (GenLoop.const : GenLoop (Fin n) Y y).val :=
    { toFun := fun q => p.symm q.1
      continuous_toFun := p.symm.continuous.comp continuous_fst
      map_zero_left := fun _ => p.symm.source
      map_one_left := fun _ => p.symm.target }
  obtain ⟨J⟩ := Path.Homotopic.trans_symm p
  apply Proofs.M40.Topology.homotopicRel_of_nullhomotopic_boundary_trace
    a GenLoop.const (H.trans K) (p.trans p.symm) ?_ J
  intro t q
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _ q
  · rfl





theorem exists_nonNull_sphere_of_nontrivial_homotopyGroup
    {Y : Type*} [TopologicalSpace Y] (n : ℕ) (y : Y)
    [Nontrivial (HomotopyGroup.Pi (n + 1) Y y)] :
    ∃ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y),
      ¬ f.Nullhomotopic := by
  classical
  obtain ⟨a, ha⟩ := exists_ne (1 : HomotopyGroup.Pi (n + 1) Y y)
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  obtain ⟨q, b, _, hboundary, e, he, _⟩ :=
    Proofs.M02.exists_sphere_genLoopEquiv
      (N := Fin (n + 1)) (ι := Fin (n + 2)) (by simp) y
  let f := e.symm p
  have hfp : f.val.comp q = p.val := (he f).symm.trans
    (congrArg Subtype.val (e.apply_symm_apply p))
  refine ⟨f.val, ?_⟩
  rintro ⟨z, ⟨H⟩⟩
  let H' : p.val.Homotopy (ContinuousMap.const _ z) :=
    (H.compContinuousMap q).cast hfp (by ext; rfl)
  let trace : Path y z :=
    { toFun := fun t => H (t, b)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := (H.apply_zero b).trans f.property
      target' := H.apply_one b }
  have htrace (t : unitInterval) (w : Cube.boundary (Fin (n + 1))) :
      H' (t, w.val) = trace t := by
    change H (t, q w.val) = H (t, b)
    rw [(hboundary w.val).mpr w.property]
  have hnull := genLoop_homotopic_const_of_uniform_nullhomotopy p H' trace htrace
  apply ha
  rw [← hp, HomotopyGroup.one_def]
  exact Quotient.sound hnull

end PoincareConjecture.M60
