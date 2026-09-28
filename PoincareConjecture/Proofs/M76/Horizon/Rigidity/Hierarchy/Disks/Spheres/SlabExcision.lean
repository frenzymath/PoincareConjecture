import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Maps.SlabExcision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Spheres.OriginalArcRemoval

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem plDomain_hamiltonZero_third_slab_of_supported_phase_avoidance
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi psi : C(H0, H0)) {R D : Set X0} (hR : IsCompact R)
    {cut a b : ℝ} (ha : cut < a) (hab : a ≤ b) (hb : b < cut + p)
    (he : PLDomain e (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)})))
    (hD : IsClosed D) (hDR : D ⊆ interior R)
    (hfixed : ∀ x ∉ D, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (havoid : ∀ x ∈ D, hamiltonZeroThirdCircleMap psi x ≠ (a : C0) ∧
      hamiltonZeroThirdCircleMap psi x ≠ (b : C0)) :
    PLDomain e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      frontier (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
          ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) ∪
            (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)})) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let q (f : C(H0, H0)) : C(R, C0) :=
    (hamiltonZeroThirdCircleMap f).comp ⟨Subtype.val, continuous_subtype_val⟩
  have hset (f : C(H0, H0)) (A : Set C0) :
      Subtype.val '' ((q f) ⁻¹' A) = R ∩ hamiltonZeroThirdCircleMap f ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, hy, rfl⟩
  have hphases (f : C(H0, H0)) :
      Subtype.val '' ((q f) ⁻¹' frontier (AddCircle.closedIntervalArc p a b)) =
        (R ∩ hamiltonZeroThirdCircleMap f ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroThirdCircleMap f ⁻¹' {(b : C0)}) := by
    rw [AddCircle.frontier_closedIntervalArc_shifted p ha hab hb]
    rw [show ({(a : C0), (b : C0)} : Set C0) = {(a : C0)} ∪ {(b : C0)} by
      ext; simp [or_comm], preimage_union, image_union, hset, hset]
  have he' : PLDomain e (Subtype.val '' ((q phi) ⁻¹' AddCircle.closedIntervalArc p a b)) := by
    rw [hset]; exact he
  have hf' : frontier (Subtype.val '' ((q phi) ⁻¹' AddCircle.closedIntervalArc p a b)) =
      (Subtype.val '' ((q phi) ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        Subtype.val '' ((q phi) ⁻¹' frontier (AddCircle.closedIntervalArc p a b)) := by
    rw [hphases, hset]; exact hfront
  obtain ⟨hPL, hf⟩ := HamiltonIntervalTorus.plDomain_relative_preimage_of_eq_off_closed
    hR (q phi) (q psi) (AddCircle.isCompact_closedIntervalArc p a b).isClosed
    he' hf' hD hDR
    (by
      intro x hx
      change hamiltonZeroThirdCircleMap psi x = hamiltonZeroThirdCircleMap phi x
      rw [hamiltonZeroThirdCircleMap_ambient, hamiltonZeroThirdCircleMap_ambient, hfixed x hx])
    (by
      intro x hx
      rw [AddCircle.frontier_closedIntervalArc_shifted p ha hab hb]
      exact fun h => h.elim (havoid x hx).1 (havoid x hx).2)
  rw [hset] at hPL
  rw [hphases, hset] at hf
  exact ⟨hPL, hf⟩

theorem plDomains_hamiltonZero_third_slabs_of_supported_phase_avoidance
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi psi : C(H0, H0)) {R D : Set X0} (hR : IsCompact R)
    {cut a b : ℝ} (ha : cut < a) (hab : a < b) (hb : b < cut + p)
    (hslabs : ∀ side : Bool,
      let N := R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)})))
    (hD : IsClosed D) (hDR : D ⊆ interior R)
    (hfixed : ∀ x ∉ D, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    (havoid : ∀ x ∈ D, hamiltonZeroThirdCircleMap psi x ≠ (a : C0) ∧
      hamiltonZeroThirdCircleMap psi x ≠ (b : C0)) :
    ∀ side : Bool,
      let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)})) := by
  intro side
  cases side
  · exact plDomain_hamiltonZero_third_slab_of_supported_phase_avoidance phi psi hR
      ha hab.le hb (hslabs false).1 (hslabs false).2 hD hDR hfixed havoid
  · have hf : frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p b (a + p)) =
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p b (a + p)) ∩
          frontier R) ∪ ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)}) ∪
            (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((a + p : ℝ) : C0)})) := by
      rw [AddCircle.coe_add_period, union_comm (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)})]
      exact (hslabs true).2
    obtain ⟨hPL, hfront⟩ := plDomain_hamiltonZero_third_slab_of_supported_phase_avoidance
      phi psi hR (cut := (a + b) / 2) (by linarith : (a + b) / 2 < b)
      (by linarith : b ≤ a + p) (by linarith : a + p < (a + b) / 2 + p)
      (hslabs true).1 hf hD hDR hfixed (by
        intro x hx
        rw [AddCircle.coe_add_period]
        exact ⟨(havoid x hx).2, (havoid x hx).1⟩)
    rw [AddCircle.coe_add_period,
      union_comm (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)})] at hfront
    exact ⟨hPL, hfront⟩

end PoincareConjecture.M76
