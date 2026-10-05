import PoincareLib.Topology.Manifold.NeckCap.Theory
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The actual covering of a punctured projective model

The frozen total cover is controlled only away from its omitted antipodal
pair. Restricting to that open domain and corestricting to its exact image
gives a proper covering with the literal antipodal fibers. This is P0 of
`tasks/M25/case-projective/plan-lifting.md`, for the projective cases of
Morgan--Tian A.21, pp. 510-514. No behavior at the removed points is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D

/-- The actual domain of a punctured standard projective cover, retained
in P0 of the projective-lifting derivation for MT A.21, pp. 510-514. -/
def projectiveCoverDomain (p : RealProjectiveThree) : Set UnitThreeSphere :=
  {x | Quotient.mk' x ≠ p}

/-- Antipodal points have the same frozen quotient class. This is the
domain-invariance step of P0 for MT A.21, pp. 510-514. -/
theorem projectiveQuotient_neg (x : UnitThreeSphere) :
    (Quotient.mk' (-x) : RealProjectiveThree) = Quotient.mk' x :=
  Quotient.sound (Or.inr rfl)

/-- The valid punctured domain is antipodally invariant. P0 of the
projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem neg_mem_projectiveCoverDomain_iff (p : RealProjectiveThree) (x : UnitThreeSphere) :
    -x ∈ projectiveCoverDomain p ↔ x ∈ projectiveCoverDomain p := by
  simp only [projectiveCoverDomain, mem_ofPred_eq, projectiveQuotient_neg]

/-- A chosen puncture representative identifies exactly the excluded
pair. P0 of the projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem projectiveCoverDomain_eq_compl_pair {p : RealProjectiveThree}
    (x : UnitThreeSphere) (hx : Quotient.mk' x = p) :
    projectiveCoverDomain p = ({x, -x} : Set UnitThreeSphere)ᶜ := by
  ext y
  change (Quotient.mk' y : RealProjectiveThree) ≠ p ↔ ¬ (y = x ∨ y = -x)
  rw [← hx]
  exact not_congr (@Quotient.eq UnitThreeSphere realProjectiveThreeSetoid y x)

/-- Removing the literal antipodal pair gives an open sphere domain,
without a separation assumption on the quotient. P0 for MT A.21. -/
theorem isOpen_projectiveCoverDomain (p : RealProjectiveThree) :
    IsOpen (projectiveCoverDomain p) := by
  obtain ⟨x, hx⟩ := Quotient.mk'_surjective p
  rw [projectiveCoverDomain_eq_compl_pair x hx]
  exact ((finite_singleton (-x)).insert x).isClosed.isOpen_compl

/-- The antipodal involution on the retained domain. P0 of the
projective-lifting derivation for MT A.21, pp. 510-514. -/
noncomputable def projectiveDomainAntipode (p : RealProjectiveThree) :
    projectiveCoverDomain p ≃ₜ projectiveCoverDomain p where
  toFun x := ⟨-x.1, (neg_mem_projectiveCoverDomain_iff p x.1).mpr x.2⟩
  invFun x := ⟨-x.1, (neg_mem_projectiveCoverDomain_iff p x.1).mpr x.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- The retained deck involution has no fixed point. P0 of the
projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem projectiveDomainAntipode_ne (p : RealProjectiveThree)
    (x : projectiveCoverDomain p) : x ≠ projectiveDomainAntipode p x := by
  intro h
  exact ne_neg_of_mem_unit_sphere ℝ x.1 (congrArg Subtype.val h)

namespace StandardPuncturedProjectiveCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}
  (C : PoincareMT.StandardPuncturedProjectiveCover Q p U)

/-- The exact image field places every valid cover value in its target.
This is the corestriction premise in P0 for MT A.21, pp. 510-514. -/
theorem cover_mem {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain p) :
    C.cover x ∈ U :=
  C.image_eq.subset (mem_image_of_mem C.cover hx)

/-- The restricted cover keeps the actual frozen forward map on its
valid domain. P0 of the projective-lifting derivation for MT A.21. -/
def restrictedCover (x : projectiveCoverDomain p) : U :=
  ⟨C.cover x.1, cover_mem C x.2⟩

/-- The restricted map is onto precisely the specified region. P0 of
the projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem restrictedCover_surjective : Function.Surjective (restrictedCover C) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := C.image_eq.symm.subset y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The restricted fibers are the two literal antipodal points. P0 of
the projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem restrictedCover_fibers (x y : projectiveCoverDomain p) :
    restrictedCover C x = restrictedCover C y ↔
      x = y ∨ x = projectiveDomainAntipode p y := by
  rw [Subtype.ext_iff]
  change C.cover x.1 = C.cover y.1 ↔ _
  rw [C.fibers x.1 y.1 x.2 y.2]
  simp only [Subtype.ext_iff, projectiveDomainAntipode]
  rfl

/-- Negating a valid point preserves its actual cover value. P0 of the
projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem cover_neg {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain p) :
    C.cover (-x) = C.cover x :=
  (C.fibers (-x) x ((neg_mem_projectiveCoverDomain_iff p x).mpr hx) hx).mpr (Or.inr rfl)

/-- Restricting to the open valid domain preserves the local charts into
the original manifold. P0 of the projective-lifting derivation for MT A.21. -/
theorem isLocalHomeomorph_domainRestrict :
    IsLocalHomeomorph (fun x : projectiveCoverDomain p => C.cover x.1) := by
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  have hval := (isOpen_projectiveCoverDomain p).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact C.local_diffeomorph.isLocalHomeomorphOn.comp hval.isLocalHomeomorphOn
    (fun x _ => x.2)

include C

/-- The exact cover image is an open region of the original manifold.
P0 of the projective-lifting derivation for MT A.21, pp. 510-514. -/
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

/-- Corestriction to the exact open image retains the same local
homeomorphisms. P0 of the projective-lifting derivation for MT A.21. -/
theorem restrictedCover_isLocalHomeomorph : IsLocalHomeomorph (restrictedCover C) := by
  apply IsLocalHomeomorph.of_comp
    (g := (Subtype.val : U → Q)) (f := restrictedCover C)
  · exact isLocalHomeomorph_domainRestrict C
  · exact (isOpen_region C).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  · exact (isLocalHomeomorph_domainRestrict C).continuous.subtype_mk _

/-- Saturation of a set under the restricted cover is its union with its
antipodal preimage. This is the closed-map argument of P0 for MT A.21. -/
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

/-- The restricted map is closed because antipodal saturation preserves
closed sets. Finite fibers alone are not used for this conclusion.
P0 of the projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem restrictedCover_isClosedMap : IsClosedMap (restrictedCover C) := by
  have hloc := restrictedCover_isLocalHomeomorph C
  have hq := hloc.isOpenMap.isQuotientMap hloc.continuous (restrictedCover_surjective C)
  intro F hF
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [restrictedCover_saturation C]
  exact hF.union (hF.preimage (projectiveDomainAntipode p).continuous)

/-- Each actual fiber of the restricted map is finite. P0 of the
projective-lifting derivation for MT A.21, pp. 510-514. -/
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

/-- The actual restricted map is a covering of the actual target region.
No covering assertion is made for the total frozen map at its removed
points. P0 of the projective-lifting derivation for MT A.21, pp. 510-514. -/
theorem restrictedCover_isCoveringMap : IsCoveringMap (restrictedCover C) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact (restrictedCover_isClosedMap C).isCoveringMapOn_of_isLocalHomeomorphOn
    (fun y _ => restrictedCover_finite_fiber C y)
    (restrictedCover_isLocalHomeomorph C).isLocalHomeomorphOn

/-- The restricted cover is proper by continuity, the proved closed-map
property, and compact finite fibers. P0 of the projective-lifting
derivation for MT A.21, pp. 510-514; its source need not be compact. -/
theorem restrictedCover_isProperMap : IsProperMap (restrictedCover C) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(restrictedCover_isLocalHomeomorph C).continuous, restrictedCover_isClosedMap C,
      fun y => (restrictedCover_finite_fiber C y).isCompact⟩

end StandardPuncturedProjectiveCover
end PoincareMT.M25.Topology3D
