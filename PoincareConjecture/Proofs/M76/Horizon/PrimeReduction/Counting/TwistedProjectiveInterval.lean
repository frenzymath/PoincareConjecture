import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ProjectiveHomology
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set CategoryTheory Limits
open scoped Topology

namespace PoincareConjecture.M76.TwistedProjectiveInterval

abbrev Cover := UnitTwoSphere × unitInterval

def deck : Cover ≃ₜ Cover := (Homeomorph.neg UnitTwoSphere).prodCongr
  unitInterval.symmHomeomorph

theorem deck_involutive : Function.Involutive deck := fun z =>
  Prod.ext (neg_neg z.1) (unitInterval.symm_symm z.2)

theorem deck_ne (z : Cover) : deck z ≠ z := fun h =>
  (ne_neg_of_mem_unit_sphere ℝ z.1) (congrArg Prod.fst h).symm

def orbitSetoid : Setoid Cover where
  r x y := x = y ∨ x = deck y
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr ((congrArg deck h).trans (deck_involutive y)).symm
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (hxy.trans hyz)
      · exact Or.inr (hxy.trans (congrArg deck hyz))
      · exact Or.inl (hxy.trans ((congrArg deck hyz).trans (deck_involutive z)))

abbrev Model := Quotient orbitSetoid

def projection : Cover → Model := Quotient.mk orbitSetoid

theorem projection_eq (x y : Cover) :
    projection x = projection y ↔ x = y ∨ x = deck y := Quotient.eq

theorem projection_deck (x : Cover) : projection (deck x) = projection x :=
  Quotient.sound (Or.inr rfl)

theorem continuous_projection : Continuous projection := continuous_quotient_mk'

instance : T2Space Model := by
  have hq := Poincare.Topology.isOpenQuotientMap_of_pair_fibers orbitSetoid deck
    deck.continuous (fun _ _ => Iff.rfl)
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have he : {z : Cover × Cover | projection z.1 = projection z.2} =
      {z | z.1 = z.2} ∪ {z | z.1 = deck z.2} := by
    ext z
    exact projection_eq z.1 z.2
  change IsClosed {z : Cover × Cover | projection z.1 = projection z.2}
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst (deck.continuous.comp continuous_snd))

theorem projection_isCoveringMap : IsCoveringMap projection := by
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  exact Poincare.Topology.Orientation.ProjectivePlane.involutionQuotient_isLocalHomeomorph
    orbitSetoid deck deck_involutive (fun z => (deck_ne z).symm) (fun _ _ => Iff.rfl)

def midpoint : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem symm_midpoint : unitInterval.symm midpoint = midpoint := by
  apply Subtype.ext
  norm_num [midpoint, unitInterval.symm]

def zeroSection : Set Model := projection '' {z | z.2 = midpoint}

def boundary : Set Model := projection '' {z | z.2 = 0 ∨ z.2 = 1}

def boundaryMap (x : UnitTwoSphere) : Model := projection (x, 0)

theorem boundaryMap_injective : Function.Injective boundaryMap := by
  intro x y h
  rcases (projection_eq (x, 0) (y, 0)).mp h with h | h
  · exact congrArg Prod.fst h
  · have ht := congrArg (fun z : Cover => (z.2 : ℝ)) h
    norm_num [deck, unitInterval.symmHomeomorph, unitInterval.symm] at ht

theorem range_boundaryMap : range boundaryMap = boundary := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(x, 0), Or.inl rfl, rfl⟩
  · rintro _ ⟨⟨x, t⟩, ht, rfl⟩
    rcases ht with ht | ht
    · exact ⟨x, congrArg projection (Prod.ext rfl ht.symm)⟩
    · refine ⟨-x, ?_⟩
      change projection (-x, 0) = projection (x, t)
      apply (projection_eq _ _).mpr
      right
      apply Prod.ext
      · rfl
      · change 0 = unitInterval.symm t
        rw [show t = 1 from ht]
        simp

noncomputable def boundaryHomeomorph : UnitTwoSphere ≃ₜ boundary :=
  ((continuous_projection.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
    boundaryMap_injective).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr range_boundaryMap)

theorem boundaryHomeomorph_apply (x : UnitTwoSphere) :
    (boundaryHomeomorph x : Model) = projection (x, 0) := rfl

theorem projection_top (x : UnitTwoSphere) :
    projection (x, 1) = (boundaryHomeomorph (-x) : Model) := by
  rw [boundaryHomeomorph_apply]
  apply (projection_eq _ _).mpr
  right
  apply Prod.ext (neg_neg x).symm
  change 1 = unitInterval.symm 0
  simp

def zeroSectionMap : RealProjectiveTwo → Model :=
  Quotient.lift (fun x : UnitTwoSphere => projection (x, midpoint)) (by
    intro x y h
    rcases h with h | h
    · exact congrArg (fun x => projection (x, midpoint)) h
    · apply (projection_eq _ _).mpr
      right
      exact Prod.ext h symm_midpoint.symm)

theorem continuous_zeroSectionMap : Continuous zeroSectionMap :=
  (continuous_projection.comp (continuous_id.prodMk continuous_const)).quotient_lift _

theorem zeroSectionMap_injective : Function.Injective zeroSectionMap := by
  intro x y h
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      rcases (projection_eq (x, midpoint) (y, midpoint)).mp h with h | h
      · exact Quotient.sound (Or.inl (congrArg Prod.fst h))
      · exact Quotient.sound (Or.inr (congrArg Prod.fst h))

theorem range_zeroSectionMap : range zeroSectionMap = zeroSection := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Quotient.inductionOn with | _ x =>
      exact ⟨(x, midpoint), rfl, rfl⟩
  · rintro _ ⟨⟨x, t⟩, ht, rfl⟩
    exact ⟨Quotient.mk realProjectiveTwoSetoid x,
      congrArg projection (Prod.ext rfl ht.symm)⟩

noncomputable def zeroSectionHomeomorph : RealProjectiveTwo ≃ₜ zeroSection :=
  (continuous_zeroSectionMap.isClosedEmbedding zeroSectionMap_injective).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_zeroSectionMap)

theorem zeroSectionHomeomorph_apply (x : UnitTwoSphere) :
    (zeroSectionHomeomorph (Quotient.mk realProjectiveTwoSetoid x) : Model) =
      projection (x, midpoint) := rfl

theorem projection_mem_zeroSection (z : Cover) :
    projection z ∈ zeroSection ↔ z.2 = midpoint := by
  constructor
  · rintro ⟨w, hw, h⟩
    rcases (projection_eq w z).mp h with h | h
    · exact (congrArg Prod.snd h).symm.trans hw
    · have he : unitInterval.symm z.2 = midpoint :=
        (congrArg Prod.snd h).symm.trans hw
      have hi := congrArg unitInterval.symm he
      simpa only [unitInterval.symm_symm, symm_midpoint] using hi
  · intro h
    exact ⟨z, h, rfl⟩

theorem projection_mem_boundary (z : Cover) :
    projection z ∈ boundary ↔ z.2 = 0 ∨ z.2 = 1 := by
  constructor
  · rintro ⟨w, hw, h⟩
    rcases (projection_eq w z).mp h with h | h
    · exact h ▸ hw
    · have he : w.2 = unitInterval.symm z.2 := congrArg Prod.snd h
      rcases hw with hw | hw
      · right
        have hi := congrArg unitInterval.symm (he.symm.trans hw)
        simpa using hi
      · left
        have hi := congrArg unitInterval.symm (he.symm.trans hw)
        simpa using hi
  · intro h
    exact ⟨z, h, rfl⟩

theorem zeroSection_disjoint_boundary : Disjoint zeroSection boundary := by
  apply disjoint_left.mpr
  intro x hx hb
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
  have hz := (projection_mem_zeroSection z).mp hx
  rcases (projection_mem_boundary z).mp hb with he | he
  · have hh := congrArg Subtype.val (hz.symm.trans he)
    norm_num [midpoint] at hh
  · have hh := congrArg Subtype.val (hz.symm.trans he)
    norm_num [midpoint] at hh


theorem exists_homology_retract (R : ModuleCat (ZMod 2)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj (TopCat.of Model)).homology R 1)
      (r : (TopCat.toSSet.obj (TopCat.of Model)).homology R 1 ⟶ R), i ≫ r = 𝟙 R := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let x : UnitTwoSphere := Classical.arbitrary _
  let f : C(UnitTwoSphere, Cover) :=
    ⟨fun y => (y, midpoint), continuous_id.prodMk continuous_const⟩
  let P := (PathConnectedSpace.somePath x (-x)).map f.continuous
  have he : deck (x, midpoint) = f (-x) := Prod.ext rfl symm_midpoint
  exact AntipodalCover.exists_homology_retract projection deck deck_involutive deck_ne
    projection_eq projection_isCoveringMap Quotient.mk_surjective R (x, midpoint)
    (P.cast rfl he)

theorem h1_not_isZero (R : ModuleCat (ZMod 2)) [Nontrivial R] :
    ¬ IsZero ((TopCat.toSSet.obj (TopCat.of Model)).homology R 1) := by
  obtain ⟨i, r, hir⟩ := exists_homology_retract R
  intro hzero
  have hi : i = 0 := hzero.eq_of_tgt i 0
  have hid : 𝟙 R = 0 := hir.symm.trans (by rw [hi, zero_comp])
  have : Subsingleton R := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero R).mpr hid)
  exact false_of_nontrivial_of_subsingleton R

end PoincareConjecture.M76.TwistedProjectiveInterval
