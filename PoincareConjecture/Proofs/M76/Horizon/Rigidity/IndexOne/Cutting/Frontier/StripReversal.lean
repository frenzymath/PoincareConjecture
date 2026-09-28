import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.OldBoundaryStrips









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

noncomputable def closedPhaseIntervalCoordinatesWide (a b : ℝ) (hgap : b < a + p) :
    Icc a b ≃ₜ AddCircle.closedIntervalArc p a b := by
  have hinj : InjOn (fun t : ℝ => (t : C)) (Icc a b) := by
    intro x hx y hy hxy
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show x ∈ Ico a (a + p) from ⟨hx.1, hx.2.trans_lt hgap⟩)
      (show y ∈ Ico a (a + p) from ⟨hy.1, hy.2.trans_lt hgap⟩)).mp hxy
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn (fun t : ℝ => (t : C)) (Icc a b) hinj)
    (((AddCircle.continuous_mk' p).comp continuous_subtype_val).subtype_mk _)

noncomputable def complementaryIntervalReversal (a b : ℝ)
    (hab : a < b) (hgap : b < a + p) : Icc a b ≃ₜ Icc b (a + p) :=
  (iccHomeoI a b hab).trans
    (unitInterval.symmHomeomorph.trans (iccHomeoI b (a + p) hgap).symm)

theorem complementaryIntervalReversal_apply (a b : ℝ)
    (hab : a < b) (hgap : b < a + p) (t : Icc a b) :
    (complementaryIntervalReversal a b hab hgap t : ℝ) =
      (a + p - b) * (1 - ((t : ℝ) - a) / (b - a)) + b := rfl

theorem complementaryIntervalReversal_left (a b : ℝ)
    (hab : a < b) (hgap : b < a + p) :
    (complementaryIntervalReversal a b hab hgap ⟨a, le_rfl, hab.le⟩ : ℝ) = a + p := by
  rw [complementaryIntervalReversal_apply]
  simp

theorem complementaryIntervalReversal_right (a b : ℝ)
    (hab : a < b) (hgap : b < a + p) :
    (complementaryIntervalReversal a b hab hgap ⟨b, hab.le, le_rfl⟩ : ℝ) = b := by
  rw [complementaryIntervalReversal_apply]
  simp [sub_ne_zero.mpr hab.ne']

noncomputable def complementaryPhaseArcReversal (a b : ℝ)
    (hab : a < b) (hgap : b < a + p) :
    AddCircle.closedIntervalArc p a b ≃ₜ AddCircle.closedIntervalArc p b (a + p) :=
  (closedPhaseIntervalCoordinatesWide a b hgap).symm.trans
    ((complementaryIntervalReversal a b hab hgap).trans
      (closedPhaseIntervalCoordinatesWide b (a + p) (by linarith)))

theorem complementaryPhaseArcReversal_fixed (a b : ℝ)
    (hab : a < b) (hgap : b < a + p)
    (z : AddCircle.closedIntervalArc p a b)
    (hz : (z : C) = (a : C) ∨ (z : C) = (b : C)) :
    (complementaryPhaseArcReversal a b hab hgap z : C) = z := by
  let E := closedPhaseIntervalCoordinatesWide a b hgap
  let t := E.symm z
  have ht : ((t : ℝ) : C) = z := congrArg Subtype.val (E.apply_symm_apply z)
  have htI : (t : ℝ) ∈ Ico a (a + p) := ⟨t.property.1, t.property.2.trans_lt hgap⟩
  change ((complementaryIntervalReversal a b hab hgap t : ℝ) : C) = z
  rcases hz with hz | hz
  · have hta : (t : ℝ) = a := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI
      (show a ∈ Ico a (a + p) from ⟨le_rfl, by norm_num⟩)).mp (ht.trans hz)
    have hteq : t = ⟨a, le_rfl, hab.le⟩ := Subtype.ext hta
    rw [hteq, complementaryIntervalReversal_left, AddCircle.coe_add_period, hz]
  · have htb : (t : ℝ) = b := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI
      (show b ∈ Ico a (a + p) from ⟨hab.le, hgap⟩)).mp (ht.trans hz)
    have hteq : t = ⟨b, hab.le, le_rfl⟩ := Subtype.ext htb
    rw [hteq, complementaryIntervalReversal_right, hz]

noncomputable def complementaryOldStripReversal (phi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (hab : a < b) (hgap : b < a + p) :
    ↥(sourceSlab phi a b ∩ frontier R) ≃ₜ
      ↥(sourceSlab phi b (a + p) ∩ frontier R) :=
  (oldSlabCoordinates phi a b F).trans
    ((Homeomorph.prodCongr (Homeomorph.refl _)
      (complementaryPhaseArcReversal a b hab hgap)).trans
      (oldSlabCoordinates phi b (a + p) F).symm)

theorem complementaryOldStripReversal_fixed (phi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (hab : a < b) (hgap : b < a + p)
    (x : ↥(sourceSlab phi a b ∩ frontier R))
    (hx : (x : X) ∈ sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) :
    (complementaryOldStripReversal phi a b F hab hgap x : X) = x := by
  let E := oldSlabCoordinates phi a b F
  let z := E x
  have hzphase : (z.2 : C) = (a : C) ∨ (z.2 : C) = (b : C) := by
    let x' : R := ⟨x, sourceSlab_subset phi a b x.property.1⟩
    have hxB : latticeHandleDomainEquiv (Fin 1) (Fin 2) L x' ∈ B :=
      (Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L) x').mpr
        x.property.2
    have hz : (z.2 : C) = sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x') :=
      (sourcePhase_eq_on_boundary phi F _ hxB).symm
    rw [hz]
    exact hx.imp ((mem_sourceSurface_iff phi (a : C) x').mp)
      ((mem_sourceSurface_iff phi (b : C) x').mp)
  have hfixed := complementaryPhaseArcReversal_fixed a b hab hgap z.2 hzphase
  change ((oldSlabCoordinates phi b (a + p) F).symm
    (z.1, complementaryPhaseArcReversal a b hab hgap z.2) : X) = x
  rw [oldSlabCoordinates_symm_original_point, hfixed]
  exact congrArg Subtype.val (E.symm_apply_apply x)

end PoincareConjecture.M76.HamiltonIntervalTorus
