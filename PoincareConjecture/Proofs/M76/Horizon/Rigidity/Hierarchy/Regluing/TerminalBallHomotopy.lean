import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBallExtension
import PoincareConjecture.Proofs.M76.Rigidity.EmbeddedParameterCoordinates










set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

noncomputable def hamiltonZeroBoxProjection : C(E3, X0) :=
  ⟨fun z => (Q0).symm ((((z.1.1 : C0), (z.1.2 : C0))), (z.2 : C0)), by fun_prop⟩

set_option backward.isDefEq.respectTransparency false in
theorem ChartwisePLBall.exists_terminalBox_relative_replacement
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {P : Set X0}
    (ball : ChartwisePLBall e P (frontier P)) (he : PLDomain e P)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (hPfirst : P ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hPsecond : P ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hPthird : P ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v)
    (boundaryMap : C(frontier P, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)))
    (hvalue : ∀ x : frontier P, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : E3).1.1) : C0), (((boundaryMap x : E3).1.2) : C0)),
        (((boundaryMap x : E3).2) : C0)))
    (hc : IsCoveringMap boundaryMap) :
    ∃ (H : ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ≃ₜ P) (f : C(P, X0)),
      ChartwisePLMap e d
        (⟨fun x => (⟨f x, mem_univ _⟩ : (univ : Set X0)),
          f.continuous.subtype_mk _⟩ : C(P, (univ : Set X0))) ∧
      (∀ x, f x = hamiltonZeroBoxProjection (H.symm x)) ∧
      (range f = hamiltonZeroBoxProjection '' ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
      (∀ x : P, (x : X0) ∈ interior P ↔
        (H.symm x : E3) ∈ interior ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
      ∃ F : (⟨fun x : P => hamiltonZeroAmbientMap phi x,
          (hamiltonZeroAmbientMap phi).continuous.comp continuous_subtype_val⟩ : C(P, X0)).HomotopyRel
          f ((Subtype.val : P → X0) ⁻¹' frontier P),
        ∀ t x, F (t, x) ∈ hamiltonZeroBoxProjection ''
          ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
  classical
  let Box : Set E3 := (Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta
  obtain ⟨H, param, hparam, hparamval, hparamfront, hHfront⟩ :=
    ball.exists_terminalBox_extension hd hphi huv hab halpha hthird hsecond hfirst
      boundaryMap hvalue hc
  let f : C(P, X0) :=
    ⟨fun x => hamiltonZeroBoxProjection (H.symm x), by fun_prop⟩
  let fu : C(P, (univ : Set X0)) :=
    ⟨fun x => ⟨f x, mem_univ _⟩, f.continuous.subtype_mk _⟩
  have hduniv : PLDomain d (univ : Set X0) :=
    ⟨hd.domain.cover, hd.domain.compatible, isClosed_univ, by simp⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKB, _⟩, _⟩, _⟩ :=
    ((isFinitePLBallPair_Icc huv).prod (isFinitePLBallPair_Icc hab)).prod
      (isFinitePLBallPair_Icc halpha)
  let x0 : P := ball.parametrization ⟨0, by simp⟩
  let q (z : E3) : P := if hz : z ∈ Box then H ⟨z, hz⟩ else x0
  have hq (z : Box) : q z = H z := by
    simp only [q, dif_pos z.property]
    rfl
  have hqc : ContinuousOn q Box := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact H.continuous.congr (fun z => (hq z).symm)
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X0)) K.space := by
    apply (hparam.restrict_finite K hK hKB.subset).congr
    intro z hz
    change param z = (q z : X0)
    rw [hq ⟨z, hKB.subset hz⟩]
    exact hparamval ⟨z, hKB.subset hz⟩
  have hfqPL : PolyhedralPLInCharts d (fun z => (fu (q z) : X0)) K.space := by
    apply (polyhedralPL_hamiltonZero_box_projection hd K hK).congr
    intro z hz
    change hamiltonZeroBoxProjection z = hamiltonZeroBoxProjection (H.symm (q z))
    rw [hq ⟨z, hKB.subset hz⟩, H.symm_apply_apply]
  have hsurj : Function.Surjective (fun z : K.space => q z) := by
    intro x
    refine ⟨⟨H.symm x, hKB.symm.subset (H.symm x).property⟩, ?_⟩
    change q (H.symm x) = x
    rw [hq (H.symm x), H.apply_symm_apply]
  have hqi : IsEmbedding (fun z : K.space => q z) := by
    have h := H.isEmbedding.comp (Homeomorph.setCongr hKB).isEmbedding
    have heq : (fun z : K.space => q z) = H ∘ Homeomorph.setCongr hKB := by
      funext z
      exact hq ⟨z, hKB.subset z.property⟩
    rw [heq]
    exact h
  have hfPL : ChartwisePLMap e d fu := by
    apply chartwisePLMap_of_embedded_polyhedral_parameters (E := E3) e d he hduniv fu
    intro x
    obtain ⟨z, hz⟩ := hsurj x
    exact ⟨K, q, z, hK, hqc.mono hKB.subset, hqi, hz,
      hsurj.range_eq.symm ▸ Filter.univ_mem, hqPL, hfqPL⟩
  have hclosed : IsClosed Box := (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
  have hinterior (x : P) : (x : X0) ∈ interior P ↔ (H.symm x : E3) ∈ interior Box := by
    have hfront := hparamfront (H.symm x)
    rw [hparamval, H.apply_symm_apply] at hfront
    rw [mem_frontier_iff_notMem_interior x.property,
      mem_frontier_iff_notMem_interior (H.symm x).property] at hfront
    exact not_iff_not.mp hfront
  have hrange : range f = hamiltonZeroBoxProjection '' Box := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨H.symm x, (H.symm x).property, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨H ⟨z, hz⟩, ?_⟩
      change hamiltonZeroBoxProjection (H.symm (H ⟨z, hz⟩)) = _
      rw [H.symm_apply_apply]
  obtain ⟨old, holdBox, holdValue, _⟩ := exists_hamiltonZero_box_coordinate_map phi
    hfirst hsecond hthird hPfirst hPsecond hPthird
  have hold (x : P) : hamiltonZeroBoxProjection (old x) = hamiltonZeroAmbientMap phi x := by
    apply (Q0).injective
    change Q0 ((Q0).symm _) = _
    rw [(Q0).apply_symm_apply]
    exact (holdValue x).symm
  have hfrontcoords (x : P) (hx : (x : X0) ∈ frontier P) : old x = (H.symm x : E3) := by
    apply hamiltonZero_box_projection_injOn hthird hsecond hfirst (holdBox x) (H.symm x).property
    change hamiltonZeroBoxProjection (old x) = hamiltonZeroBoxProjection (H.symm x)
    rw [hold, hHfront ⟨x, hx⟩]
    apply (Q0).injective
    change Q0 (hamiltonZeroAmbientMap phi x) = Q0 ((Q0).symm _)
    rw [(Q0).apply_symm_apply]
    exact hvalue ⟨x, hx⟩
  let blend (t : unitInterval) (x : P) : E3 :=
    (1 - (t : ℝ)) • old x + (t : ℝ) • (H.symm x : E3)
  have hblend (t : unitInterval) (x : P) : blend t x ∈ Box :=
    (((convex_Icc u v).prod (convex_Icc a b)).prod (convex_Icc alpha beta))
      (holdBox x) (H.symm x).property (sub_nonneg.mpr t.property.2) t.property.1
        (sub_add_cancel _ _)
  let F : (⟨fun x : P => hamiltonZeroAmbientMap phi x,
      (hamiltonZeroAmbientMap phi).continuous.comp continuous_subtype_val⟩ : C(P, X0)).HomotopyRel
      f ((Subtype.val : P → X0) ⁻¹' frontier P) :=
    { toFun := fun z => hamiltonZeroBoxProjection (blend z.1 z.2)
      continuous_toFun := by dsimp [blend]; fun_prop
      map_zero_left := by intro x; simpa [blend] using hold x
      map_one_left := by intro x; simp [blend, f]
      prop' := by
        intro t x hx
        change hamiltonZeroBoxProjection (blend t x) = hamiltonZeroAmbientMap phi x
        dsimp [blend]
        rw [← hfrontcoords x hx, ← add_smul, sub_add_cancel, one_smul, hold] }
  exact ⟨H, f, hfPL, fun _ => rfl, hrange, hinterior, F,
    fun t x => ⟨blend t x, hblend t x, rfl⟩⟩

end PoincareConjecture.M76
