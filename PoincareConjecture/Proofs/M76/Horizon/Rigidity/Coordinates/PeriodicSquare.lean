import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient











set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.PeriodicSquare

variable (p : ℝ) [Fact (0 < p)]

abbrev Square := Icc (0 : ℝ) p × Icc (0 : ℝ) p

def projection : C(Square p, AddCircle p × AddCircle p) :=
  ⟨fun z => ((z.1 : ℝ), (z.2 : ℝ)),
    ((AddCircle.continuous_mk' p).comp
      (continuous_subtype_val.comp continuous_fst)).prodMk
    ((AddCircle.continuous_mk' p).comp
      (continuous_subtype_val.comp continuous_snd))⟩

theorem surjective_projection : Function.Surjective (projection p) := by
  intro z
  obtain ⟨s, hs, hsz⟩ := AddCircle.eq_coe_Ico z.1
  obtain ⟨t, ht, htz⟩ := AddCircle.eq_coe_Ico z.2
  exact ⟨(⟨s, hs.1, hs.2.le⟩, ⟨t, ht.1, ht.2.le⟩), Prod.ext hsz htz⟩

theorem isQuotientMap_projection : IsQuotientMap (projection p) :=
  .of_surjective_continuous (surjective_projection p) (projection p).continuous

def SidePair (z w : Square p) : Prop :=
  ((z.1 : ℝ) = 0 ∧ (w.1 : ℝ) = p ∧ z.2 = w.2) ∨
    ((z.2 : ℝ) = 0 ∧ (w.2 : ℝ) = p ∧ z.1 = w.1)

omit [Fact (0 < p)] in
theorem projection_eq_of_sidePair {z w : Square p} (h : SidePair p z w) :
    projection p z = projection p w := by
  rcases h with ⟨hz, hw, ht⟩ | ⟨hz, hw, hs⟩
  · apply Prod.ext
    · change ((z.1 : ℝ) : AddCircle p) = ((w.1 : ℝ) : AddCircle p)
      rw [hz, hw, AddCircle.coe_zero, AddCircle.coe_period]
    · exact congrArg (fun t : Icc (0 : ℝ) p => ((t : ℝ) : AddCircle p)) ht
  · apply Prod.ext
    · exact congrArg (fun s : Icc (0 : ℝ) p => ((s : ℝ) : AddCircle p)) hs
    · change ((z.2 : ℝ) : AddCircle p) = ((w.2 : ℝ) : AddCircle p)
      rw [hz, hw, AddCircle.coe_zero, AddCircle.coe_period]

theorem projection_eq_iff {z w : Square p} :
    projection p z = projection p w ↔ Relation.EqvGen (SidePair p) z w := by
  constructor
  · intro h
    have hs := (AddCircle.coe_eq_coe_iff_eq_or_endpoints z.1.property w.1.property).mp
      (congrArg Prod.fst h)
    have ht := (AddCircle.coe_eq_coe_iff_eq_or_endpoints z.2.property w.2.property).mp
      (congrArg Prod.snd h)
    apply Relation.EqvGen.trans (y := (w.1, z.2))
    · rcases hs with hs | ⟨hz, hw⟩ | ⟨hz, hw⟩
      · have he : z.1 = w.1 := Subtype.ext hs
        rw [← he]
        exact .refl z
      · exact .rel _ _ (Or.inl ⟨hz, hw, rfl⟩)
      · exact .symm _ _ (.rel _ _ (Or.inl ⟨hw, hz, rfl⟩))
    · rcases ht with ht | ⟨hz, hw⟩ | ⟨hz, hw⟩
      · have he : z.2 = w.2 := Subtype.ext ht
        simpa only [he] using Relation.EqvGen.refl (r := SidePair p) w
      · exact .rel _ _ (Or.inr ⟨hz, hw, rfl⟩)
      · exact .symm _ _ (.rel _ _ (Or.inr ⟨hw, hz, rfl⟩))
  · intro h
    induction h with
    | rel z w h => exact projection_eq_of_sidePair p h
    | refl z => rfl
    | symm z w h ih => exact ih.symm
    | trans z w v hzw hwv ihzw ihwv => exact ihzw.trans ihwv

theorem sidePair_setoid_eq :
    Relation.EqvGen.setoid (SidePair p) = Setoid.ker (projection p) := by
  ext z w
  exact (projection_eq_iff p).symm

noncomputable def quotientHomeomorph :
    Quotient (Relation.EqvGen.setoid (SidePair p)) ≃ₜ AddCircle p × AddCircle p :=
  (Homeomorph.Quotient.congrRight (fun _ _ => (projection_eq_iff p).symm)).trans
    (isQuotientMap_projection p).homeomorph

@[simp] theorem quotientHomeomorph_mk (z : Square p) :
    quotientHomeomorph p (Quotient.mk _ z) = projection p z := rfl

theorem projection_eq_zero_iff (z : Square p) :
    projection p z = 0 ↔
      ((z.1 : ℝ) = 0 ∨ (z.1 : ℝ) = p) ∧
        ((z.2 : ℝ) = 0 ∨ (z.2 : ℝ) = p) := by
  change (((z.1 : ℝ) : AddCircle p), ((z.2 : ℝ) : AddCircle p)) = (0, 0) ↔ _
  rw [Prod.mk.injEq, AddCircle.coe_eq_zero_iff_endpoints z.1.property,
    AddCircle.coe_eq_zero_iff_endpoints z.2.property]




theorem exists_homeomorph_of_square_map {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : C(Square p, X)) (hf : Function.Surjective f)
    (hfib : ∀ z w, f z = f w ↔ Relation.EqvGen (SidePair p) z w) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ X,
      ∀ z, h (projection p z) = f z := by
  have hq : IsQuotientMap f := .of_surjective_continuous hf f.continuous
  let e : Quotient (Setoid.ker (projection p)) ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight
      (fun z w => (projection_eq_iff p).trans (hfib z w).symm)
  refine ⟨(isQuotientMap_projection p).homeomorph.symm.trans
    (e.trans hq.homeomorph), ?_⟩
  intro z
  change hq.homeomorph (e ((isQuotientMap_projection p).homeomorph.symm
    ((isQuotientMap_projection p).homeomorph (Quotient.mk _ z)))) = f z
  rw [Homeomorph.symm_apply_apply]
  rfl

end PoincareConjecture.M76.PeriodicSquare
