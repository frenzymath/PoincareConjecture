import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.LocalOrientation
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardAtlasExistence
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerPeriodLattice

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace AddMonoidHom

theorem exists_positiveThreeAtlas_of_quotient
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup X] [TopologicalSpace X]
    (p : E →+ X) (hp : IsLocalHomeomorph p) (hsurj : Function.Surjective p)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Nonempty (Poincare.Topology.PositiveThreeAtlas X) := by
  classical
  let V := EuclideanSpace ℝ (Fin 3)
  obtain ⟨c, hcover, _, hinv⟩ :=
    p.exists_piecewiseAffine_quotient_cover hp hsurj L.toContinuousAffineEquiv
  change ∀ i y, (c i).symm y = p (L.symm y) at hinv
  have hpositive (i j : E) (x : X) (hi : x ∈ (c i).source)
      (hj : x ∈ (c j).source) :
      0 < (fderiv ℝ (fun y => c j ((c i).symm y)) (c i x)).toLinearMap.det := by
    let delta := L.symm (c j x) - L.symm (c i x)
    have hquot (k : E) (hk : x ∈ (c k).source) : p (L.symm (c k x)) = x := by
      rw [← hinv k (c k x)]
      exact (c k).left_inv hk
    have hdelta : p delta = 0 := by
      change p (L.symm (c j x) - L.symm (c i x)) = 0
      rw [map_sub, hquot j hj, hquot i hi, sub_self]
    let a : V → V := fun y => L delta + y
    have ha (y : V) : L.symm (a y) = delta + L.symm y := by
      simp only [a, map_add, L.symm_apply_apply]
    have hax : a (c i x) = c j x := by
      simp only [a, delta, map_sub, L.apply_symm_apply, sub_add_cancel]
    have hsame (y : V) : (c j).symm (a y) = (c i).symm y := by
      rw [hinv, hinv, ha, map_add, hdelta, zero_add]
    have hlocal : (fun y => c j ((c i).symm y)) =ᶠ[𝓝 (c i x)] a := by
      have hopen : IsOpen (a ⁻¹' (c j).target) :=
        (c j).open_target.preimage (continuous_const.add continuous_id)
      have hx : c i x ∈ a ⁻¹' (c j).target := by
        change a (c i x) ∈ (c j).target
        rw [hax]
        exact (c j).mapsTo hj
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [← hsame y]
      exact (c j).right_inv hy
    have hd : HasFDerivAt (fun y => c j ((c i).symm y))
        (ContinuousLinearMap.id ℝ V) (c i x) :=
      ((hasFDerivAt_id (c i x)).const_add (L delta)).congr_of_eventuallyEq hlocal
    rw [hd.fderiv]
    change 0 < (LinearMap.id : V →ₗ[ℝ] V).det
    rw [LinearMap.det_id]
    norm_num
  let choose : X → E := fun x => (hcover x).choose
  refine ⟨{
    charts := {
      atlas := Set.range c
      chartAt := fun x => c (choose x)
      mem_chart_source := fun x => (hcover x).choose_spec
      chart_mem_atlas := fun x => ⟨choose x, rfl⟩ }
    positive_transition := ?_ }⟩
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩ x ⟨hi, hj⟩
  exact hpositive i j x hi hj

end AddMonoidHom

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L

theorem hamiltonIntervalTorusAmbient_positiveThreeAtlas :
    Nonempty (Poincare.Topology.PositiveThreeAtlas X) := by
  let E := (Fin 1 → ℝ) × (Fin 2 → ℝ)
  let lattice := hamiltonLowerPeriodLattice (Fin 2)
  let : DiscreteTopology lattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (hamiltonLowerPeriodLattice (Fin 2)))
  let p : E →+ X :=
    (AddMonoidHom.id (Fin 1 → ℝ)).prodMap (QuotientAddGroup.mk' lattice.toAddSubgroup)
  have hq : IsCoveringMap
      (QuotientAddGroup.mk : (Fin 2 → ℝ) → ((Fin 2 → ℝ) ⧸ lattice.toAddSubgroup)) :=
    (lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap
  have hp : IsLocalHomeomorph p := hq.id_prod.isLocalHomeomorph
  have hsurj : Function.Surjective p := by
    rintro ⟨x, y⟩
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨(x, z), rfl⟩
  let a : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofFinrankEq _ _ (by
      simp [E, Module.finrank_prod, finrank_euclideanSpace])).toContinuousLinearEquiv
  exact p.exists_positiveThreeAtlas_of_quotient hp hsurj a

theorem hamiltonIntervalTorusAmbient_localOrientation :
    Nonempty (Poincare.Topology.Orientation.ProjectivePlane.LocalOrientation X) := by
  let e := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := e.isEmbedding.t2Space
  let : SecondCountableTopology X := e.isEmbedding.secondCountableTopology
  obtain ⟨P⟩ := hamiltonIntervalTorusAmbient_positiveThreeAtlas
  exact Poincare.Topology.Orientation.ProjectivePlane.exists_localOrientation_of_positiveThreeAtlas P

end PoincareConjecture.M76.HamiltonIntervalTorus
