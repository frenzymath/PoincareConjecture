import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.ComplementarySlabContraction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalPhaseSelectionPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.SupportedSlabDomain

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_closed_phase_region_cancellation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {D : Set X0} (hD : IsClosed D)
    {cut a b lambda : ℝ} (ha : cut < a) (hb : b < cut + p)
    (hlambda : lambda ∈ Icc a b)
    (hrange : D ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hfront : ∀ x ∈ frontier D, hamiltonZeroCircleMap phi x = (lambda : C0)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      (∀ x ∈ D, hamiltonZeroAmbientMap psi x =
        hamiltonZeroTargetPhaseRetraction lambda (hamiltonZeroAmbientMap phi x)) ∧
      (∀ theta : C0, theta ≠ (lambda : C0) →
        hamiltonZeroCircleMap psi ⁻¹' {theta} = (hamiltonZeroCircleMap phi ⁻¹' {theta}) \ D) ∧
      (∀ A : Set C0, IsClosed A → (lambda : C0) ∉ frontier A →
        PLDomain e (hamiltonZeroCircleMap phi ⁻¹' A) →
        frontier (hamiltonZeroCircleMap phi ⁻¹' A) = hamiltonZeroCircleMap phi ⁻¹' frontier A →
        PLDomain e (hamiltonZeroCircleMap psi ⁻¹' A) ∧
          frontier (hamiltonZeroCircleMap psi ⁻¹' A) = hamiltonZeroCircleMap psi ⁻¹' frontier A) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior D)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1 = (Q0 (hamiltonZeroAmbientMap phi x)).1) ∧
        ∀ t x, x ∈ D → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p a b := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let u : C(D, X0) := (hamiltonZeroAmbientMap phi).comp ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(D, (C0 × C0) × C0) := ⟨fun x => Q0 (u x), (Q0).continuous.comp u.continuous⟩
  obtain ⟨T, hT⟩ := AddCircle.exists_shifted_closedArc_normal_contraction p
    ha hb hlambda f (fun x => hrange x.property)
  let H : C(unitInterval × D, X0) := ⟨fun z => (Q0).symm (T z), by fun_prop⟩
  have hHzero (x : D) : H (0, x) = hamiltonZeroAmbientMap phi x := by
    change (Q0).symm (T (0, x)) = _
    rw [T.apply_zero]
    exact (Q0).symm_apply_apply _
  have hHone (x : D) : H (1, x) =
      hamiltonZeroTargetPhaseRetraction lambda (hamiltonZeroAmbientMap phi x) := by
    change (Q0).symm (T (1, x)) = _
    rw [T.apply_one]
    rfl
  let outer : C(unitInterval × X0, X0) :=
    (hamiltonZeroAmbientMap phi).comp ⟨Prod.snd, continuous_snd⟩
  obtain ⟨G, hGin, hGout⟩ := ContinuousMap.exists_paste_of_eq_on_frontier hD H outer (by
    intro t x hx
    change (Q0).symm (T (t, x)) = hamiltonZeroAmbientMap phi x
    rw [T.eq_fst t (hfront x hx)]
    exact (Q0).symm_apply_apply _)
  have hzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    by_cases hx : x ∈ D
    · exact (hGin 0 ⟨x, hx⟩).trans (hHzero ⟨x, hx⟩)
    · exact hGout 0 x (fun h => hx (interior_subset h))
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap g
  have hg (x : X0) : hamiltonZeroAmbientMap psi x = g x := by
    rw [hamiltonZeroAmbientMap_handle]
  have hone (x : X0) (hx : x ∈ D) : hamiltonZeroAmbientMap psi x =
      hamiltonZeroTargetPhaseRetraction lambda (hamiltonZeroAmbientMap phi x) :=
    (hg x).trans ((hGin 1 ⟨x, hx⟩).trans (hHone ⟨x, hx⟩))
  have hout (x : X0) (hx : x ∉ interior D) :
      hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x :=
    (hg x).trans (hGout 1 x hx)
  have hnormal (x : X0) (hx : x ∈ D) : hamiltonZeroCircleMap psi x = (lambda : C0) := by
    rw [← hamiltonZeroAmbientMap_circle, hone x hx,
      hamiltonZeroTargetPhaseRetraction_coordinates]
  refine ⟨psi, ?_, ⟨hamiltonZeroHandleHomotopy phi G hzero⟩,
    ⟨F.trans (hamiltonZeroHandleHomotopy phi G hzero)⟩, hone, ?_, ?_, ?_⟩
  · rw [hamiltonZeroHandleMap_domain]
    apply chartwisePL_hamiltonZero_of_phase_selection hd hphi lambda g
    intro x
    by_cases hx : x ∈ D
    · exact Or.inr ((hg x).symm.trans (hone x hx))
    · exact Or.inl ((hg x).symm.trans (hout x (fun h => hx (interior_subset h))))
  · intro theta htheta
    ext x
    by_cases hx : x ∈ D
    · simp only [mem_preimage, mem_singleton_iff, hnormal x hx,
        htheta.symm, mem_sdiff, hx, not_true_eq_false, and_false]
    · have heq : hamiltonZeroCircleMap psi x = hamiltonZeroCircleMap phi x := by
        rw [← hamiltonZeroAmbientMap_circle, hout x (fun h => hx (interior_subset h)),
          hamiltonZeroAmbientMap_circle]
      simp only [mem_preimage, mem_singleton_iff, heq, mem_sdiff, hx,
        not_false_eq_true, and_true]
  · intro A hA hlA he hAfront
    apply he.preimage_of_eq_off_closed (hamiltonZeroCircleMap phi)
      (hamiltonZeroCircleMap psi) hA hAfront hD
    · intro x hx
      rw [← hamiltonZeroAmbientMap_circle, hout x (fun h => hx (interior_subset h)),
        hamiltonZeroAmbientMap_circle]
    · apply disjoint_left.mpr
      intro x hx hxD
      exact hlA (hnormal x hxD ▸ hx)
  · refine ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hzero
      map_one_left := fun x => (hg x).symm
      prop' := hGout }, ?_, ?_⟩
    · intro t x
      by_cases hx : x ∈ D
      · change (Q0 (G (t, x))).1 = _
        rw [hGin t ⟨x, hx⟩]
        change (Q0 ((Q0).symm (T (t, ⟨x, hx⟩)))).1 = _
        rw [(Q0).apply_symm_apply]
        exact (hT t ⟨x, hx⟩).1
      · change (Q0 (G (t, x))).1 = _
        rw [hGout t x (fun h => hx (interior_subset h))]
        rfl
    · intro t x hx
      change (Q0 (G (t, x))).2 ∈ _
      rw [hGin t ⟨x, hx⟩]
      change (Q0 ((Q0).symm (T (t, ⟨x, hx⟩)))).2 ∈ _
      rw [(Q0).apply_symm_apply]
      exact (hT t ⟨x, hx⟩).2.1

theorem exists_hamiltonZero_closed_phase_pair_cancellation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {D T₀ T₁ : Set X0} (hD : IsClosed D)
    {cut a b lambda : ℝ} (ha : cut < a) (hb : b < cut + p)
    (hlambda : lambda ∈ Icc a b)
    (hrange : D ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hfront : ∀ x ∈ frontier D, hamiltonZeroCircleMap phi x = (lambda : C0))
    {theta mu : C0} (htheta : theta ≠ (lambda : C0)) (hmu : mu ≠ (lambda : C0))
    (hpair : D ∩ (hamiltonZeroCircleMap phi ⁻¹' {theta}) = T₀ ∪ T₁)
    (hprotected : Disjoint D (hamiltonZeroCircleMap phi ⁻¹' {mu})) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi ⁻¹' {theta} =
        (hamiltonZeroCircleMap phi ⁻¹' {theta}) \ (T₀ ∪ T₁) ∧
      hamiltonZeroCircleMap psi ⁻¹' {mu} = hamiltonZeroCircleMap phi ⁻¹' {mu} ∧
      (∀ A : Set C0, IsClosed A → (lambda : C0) ∉ frontier A →
        PLDomain e (hamiltonZeroCircleMap phi ⁻¹' A) →
        frontier (hamiltonZeroCircleMap phi ⁻¹' A) = hamiltonZeroCircleMap phi ⁻¹' frontier A →
        PLDomain e (hamiltonZeroCircleMap psi ⁻¹' A) ∧
          frontier (hamiltonZeroCircleMap psi ⁻¹' A) = hamiltonZeroCircleMap psi ⁻¹' frontier A) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior D)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1 = (Q0 (hamiltonZeroAmbientMap phi x)).1) ∧
        ∀ t x, x ∈ D → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p a b := by
  obtain ⟨psi, hpsi, Hpsi, Fpsi, _, hremove, hdomains, G, htangent, harc⟩ :=
    exists_hamiltonZero_closed_phase_region_cancellation hd hphi F hD ha hb hlambda hrange hfront
  refine ⟨psi, hpsi, Hpsi, Fpsi, ?_, ?_, hdomains, G, htangent, harc⟩
  · rw [hremove theta htheta, ← hpair]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  · rw [hremove mu hmu]
    exact sdiff_eq_left.mpr hprotected.symm

end PoincareConjecture.M76
