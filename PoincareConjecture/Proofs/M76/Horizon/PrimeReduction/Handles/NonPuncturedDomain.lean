import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.LatticeHandleGroups










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Circle" => AddCircle (1 : ℝ)

theorem HasPuncturedSphereModel.not_circle_retraction
    {X E α : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}
    (hm : HasPuncturedSphereModel e f R)
    (s : C(Circle, R)) (r : C(R, Circle)) :
    ¬ Function.LeftInverse r s := by
  intro hleft
  obtain ⟨_, n, A, b, M, G, C, hA, hdis, _, _, _⟩ := hm
  let H := G.trans C
  let rho := r.comp ⟨H.symm, H.symm.continuous⟩
  let sigma : C(Circle, _) := ⟨fun z => H (s z), H.continuous.comp s.continuous⟩
  let gamma := (AddCircle.periodLoop 1).map sigma.continuous
  have h := CubicalThreeSphere.circle_map_loop_nullhomotopic_of_isOpen
    A b (fun i => (hA i).1) (fun i => (hA i).2.1) hdis
    (fun i => (hA i).2.2) rho (sigma 0) gamma
  have hcomp : rho.comp sigma = ContinuousMap.id Circle := by
    ext z
    change r (H.symm (H (s z))) = z
    rw [H.symm_apply_apply]
    exact hleft z
  change (((AddCircle.periodLoop 1).map sigma.continuous).map rho.continuous).Homotopic
    (Path.refl ((rho.comp sigma) 0)) at h
  rw [Path.map_map] at h
  change ((AddCircle.periodLoop 1).map (rho.comp sigma).continuous).Homotopic
    (Path.refl ((rho.comp sigma) 0)) at h
  rw [hcomp] at h
  exact AddCircle.periodLoop_not_homotopic_refl 1 (by simpa using h)

theorem not_hasPuncturedSphereModel_latticeHandleDomain
    {ι κ α E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {f : LatticeHandleAmbient ι κ L → E}
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hindex : Fintype.card ι ≤ 2) :
    ¬ HasPuncturedSphereModel e f (latticeHandleDomain ι κ L) := by
  intro hm
  let : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  let x : LatticeHandle ι κ L := ⟨⟨0, mem_closedBall_self zero_le_one⟩, 0⟩
  obtain ⟨s, r, _, hleft⟩ := exists_lattice_handle_circle_retraction L x
  let H := latticeHandleDomainEquiv ι κ L
  let q := AddCircle.homeomorphAddCircle (4 * (128 : ℝ)) 1 (by norm_num) one_ne_zero
  let s' : C(Circle, latticeHandleDomain ι κ L) :=
    ⟨fun z => H.symm (s (q.symm z)), H.symm.continuous.comp (s.continuous.comp q.symm.continuous)⟩
  let r' : C(latticeHandleDomain ι κ L, Circle) :=
    ⟨fun z => q (r (H z)), q.continuous.comp (r.continuous.comp H.continuous)⟩
  apply hm.not_circle_retraction s' r'
  intro z
  change q (r (H (H.symm (s (q.symm z))))) = z
  rw [H.apply_symm_apply, hleft, q.apply_symm_apply]

end PoincareConjecture.M76
