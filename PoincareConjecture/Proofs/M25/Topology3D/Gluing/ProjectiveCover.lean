import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D



def projectiveCoverDomain (p : RealProjectiveThree) : Set UnitThreeSphere :=
  {x | Quotient.mk' x ≠ p}



theorem projectiveQuotient_neg (x : UnitThreeSphere) :
    (Quotient.mk' (-x) : RealProjectiveThree) = Quotient.mk' x :=
  Quotient.sound (Or.inr rfl)



theorem neg_mem_projectiveCoverDomain_iff (p : RealProjectiveThree) (x : UnitThreeSphere) :
    -x ∈ projectiveCoverDomain p ↔ x ∈ projectiveCoverDomain p := by
  simp only [projectiveCoverDomain, mem_ofPred_eq, projectiveQuotient_neg]



theorem projectiveCoverDomain_eq_compl_pair {p : RealProjectiveThree}
    (x : UnitThreeSphere) (hx : Quotient.mk' x = p) :
    projectiveCoverDomain p = ({x, -x} : Set UnitThreeSphere)ᶜ := by
  ext y
  change (Quotient.mk' y : RealProjectiveThree) ≠ p ↔ ¬ (y = x ∨ y = -x)
  rw [← hx]
  exact not_congr (@Quotient.eq UnitThreeSphere realProjectiveThreeSetoid y x)



theorem isOpen_projectiveCoverDomain (p : RealProjectiveThree) :
    IsOpen (projectiveCoverDomain p) := by
  obtain ⟨x, hx⟩ := Quotient.mk'_surjective p
  rw [projectiveCoverDomain_eq_compl_pair x hx]
  exact ((finite_singleton (-x)).insert x).isClosed.isOpen_compl



noncomputable def projectiveDomainAntipode (p : RealProjectiveThree) :
    projectiveCoverDomain p ≃ₜ projectiveCoverDomain p where
  toFun x := ⟨-x.1, (neg_mem_projectiveCoverDomain_iff p x.1).mpr x.2⟩
  invFun x := ⟨-x.1, (neg_mem_projectiveCoverDomain_iff p x.1).mpr x.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _



theorem projectiveDomainAntipode_ne (p : RealProjectiveThree)
    (x : projectiveCoverDomain p) : x ≠ projectiveDomainAntipode p x := by
  intro h
  exact ne_neg_of_mem_unit_sphere ℝ x.1 (congrArg Subtype.val h)

namespace StandardPuncturedProjectiveCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}
  (C : PoincareConjecture.StandardPuncturedProjectiveCover Q p U)



theorem cover_mem {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain p) :
    C.cover x ∈ U :=
  C.image_eq.subset (mem_image_of_mem C.cover hx)



def restrictedCover (x : projectiveCoverDomain p) : U :=
  ⟨C.cover x.1, cover_mem C x.2⟩



theorem restrictedCover_surjective : Function.Surjective (restrictedCover C) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := C.image_eq.symm.subset y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩



theorem restrictedCover_fibers (x y : projectiveCoverDomain p) :
    restrictedCover C x = restrictedCover C y ↔
      x = y ∨ x = projectiveDomainAntipode p y := by
  rw [Subtype.ext_iff]
  change C.cover x.1 = C.cover y.1 ↔ _
  rw [C.fibers x.1 y.1 x.2 y.2]
  simp only [Subtype.ext_iff, projectiveDomainAntipode]
  rfl



theorem cover_neg {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain p) :
    C.cover (-x) = C.cover x :=
  (C.fibers (-x) x ((neg_mem_projectiveCoverDomain_iff p x).mpr hx) hx).mpr (Or.inr rfl)



theorem isLocalHomeomorph_domainRestrict :
    IsLocalHomeomorph (fun x : projectiveCoverDomain p => C.cover x.1) := by
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  have hval := (isOpen_projectiveCoverDomain p).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact C.local_diffeomorph.isLocalHomeomorphOn.comp hval.isLocalHomeomorphOn
    (fun x _ => x.2)

include C



theorem isOpen_region : IsOpen U := by
  have heq : range (fun x : projectiveCoverDomain p => C.cover x.1) = U := by
    apply Eq.trans _ C.image_eq
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← heq]
  exact (isLocalHomeomorph_domainRestrict C).isOpenMap.isOpen_range



theorem restrictedCover_isLocalHomeomorph : IsLocalHomeomorph (restrictedCover C) := by
  apply IsLocalHomeomorph.of_comp
    (g := (Subtype.val : U → Q)) (f := restrictedCover C)
  · exact isLocalHomeomorph_domainRestrict C
  · exact (isOpen_region C).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  · exact (isLocalHomeomorph_domainRestrict C).continuous.subtype_mk _



theorem restrictedCover_saturation (F : Set (projectiveCoverDomain p)) :
    restrictedCover C ⁻¹' (restrictedCover C '' F) =
      F ∪ projectiveDomainAntipode p ⁻¹' F := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    rcases (restrictedCover_fibers C y x).mp heq with h | h
    · exact Or.inl (h ▸ hy)
    · exact Or.inr (show projectiveDomainAntipode p x ∈ F from h ▸ hy)
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · refine ⟨projectiveDomainAntipode p x, hx, ?_⟩
      exact (restrictedCover_fibers C _ _).mpr (Or.inr rfl)




theorem restrictedCover_isClosedMap : IsClosedMap (restrictedCover C) := by
  have hloc := restrictedCover_isLocalHomeomorph C
  have hq := hloc.isOpenMap.isQuotientMap hloc.continuous (restrictedCover_surjective C)
  intro F hF
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [restrictedCover_saturation C]
  exact hF.union (hF.preimage (projectiveDomainAntipode p).continuous)



theorem restrictedCover_finite_fiber (y : U) :
    (restrictedCover C ⁻¹' {y}).Finite := by
  obtain ⟨x, rfl⟩ := restrictedCover_surjective C y
  have heq : restrictedCover C ⁻¹' {restrictedCover C x} =
      ({x, projectiveDomainAntipode p x} : Set (projectiveCoverDomain p)) := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, restrictedCover_fibers C,
      mem_insert_iff]
  rw [heq]
  exact (finite_singleton _).insert _




theorem restrictedCover_isCoveringMap : IsCoveringMap (restrictedCover C) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact (restrictedCover_isClosedMap C).isCoveringMapOn_of_isLocalHomeomorphOn
    (fun y _ => restrictedCover_finite_fiber C y)
    (restrictedCover_isLocalHomeomorph C).isLocalHomeomorphOn




theorem restrictedCover_isProperMap : IsProperMap (restrictedCover C) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(restrictedCover_isLocalHomeomorph C).continuous, restrictedCover_isClosedMap C,
      fun y => (restrictedCover_finite_fiber C y).isCompact⟩

end StandardPuncturedProjectiveCover
end PoincareConjecture.M25.Topology3D
