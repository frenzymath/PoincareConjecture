import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ProjectiveCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

abbrev PuncturedProjectiveSphere (p : RealProjectiveThree) :=
  {q : UnitThreeSphere // Quotient.mk' q ≠ p}

theorem isOpen_puncturedProjectiveSphere (p : RealProjectiveThree) :
    IsOpen {q : UnitThreeSphere | Quotient.mk' q ≠ p} := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective p
  have he : {q : UnitThreeSphere | Quotient.mk' q ≠ Quotient.mk' a} = {a, -a}ᶜ := by
    ext q
    simp only [mem_ofPred_eq, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
    exact not_congr Quotient.eq
  change IsOpen {q : UnitThreeSphere | Quotient.mk' q ≠ Quotient.mk' a}
  rw [he]
  exact ((finite_singleton (-a)).insert a).isClosed.isOpen_compl

namespace PuncturedProjectiveSphere

def antipode {p : RealProjectiveThree} (q : PuncturedProjectiveSphere p) :
    PuncturedProjectiveSphere p :=
  ⟨-q.val, fun h => q.property ((Quotient.sound (Or.inr rfl)).symm.trans h)⟩

@[simp] theorem antipode_antipode {p : RealProjectiveThree}
    (q : PuncturedProjectiveSphere p) : antipode (antipode q) = q := by
  apply Subtype.ext
  exact neg_neg _

theorem continuous_antipode (p : RealProjectiveThree) :
    Continuous (antipode : PuncturedProjectiveSphere p → PuncturedProjectiveSphere p) :=
  continuous_subtype_val.neg.subtype_mk _

theorem ne_antipode {p : RealProjectiveThree} (q : PuncturedProjectiveSphere p) :
    q ≠ antipode q := by
  intro h
  exact ne_neg_of_mem_unit_sphere ℝ q.val (congrArg Subtype.val h)

end PuncturedProjectiveSphere

namespace StandardPuncturedProjectiveCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}
  (S : StandardPuncturedProjectiveCover Q p U)

def restrictedCover : PuncturedProjectiveSphere p → U :=
  fun q => ⟨S.cover q, S.image_eq.subset (mem_image_of_mem S.cover q.property)⟩

theorem restrictedCover_surjective : Function.Surjective S.restrictedCover := by
  intro y
  have hy : (y : Q) ∈ S.cover '' {x | Quotient.mk' x ≠ p} := by
    rw [S.image_eq]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem restrictedCover_eq_iff (x y : PuncturedProjectiveSphere p) :
    S.restrictedCover x = S.restrictedCover y ↔
      x = y ∨ x = PuncturedProjectiveSphere.antipode y := by
  constructor
  · intro h
    rcases (S.fibers x y x.property y.property).mp (congrArg Subtype.val h) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · intro h
    apply Subtype.ext
    apply (S.fibers x y x.property y.property).mpr
    rcases h with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem restrictedCover_fiber (x : PuncturedProjectiveSphere p) :
    S.restrictedCover ⁻¹' {S.restrictedCover x} =
      {x, PuncturedProjectiveSphere.antipode x} := by
  ext y
  exact S.restrictedCover_eq_iff y x

theorem restrictedCover_finite_fiber (y : U) :
    (S.restrictedCover ⁻¹' {y}).Finite := by
  obtain ⟨x, rfl⟩ := S.restrictedCover_surjective y
  rw [S.restrictedCover_fiber]
  exact (finite_singleton _).insert _

private theorem isLocalHomeomorph_domRestrict :
    IsLocalHomeomorph (fun q : PuncturedProjectiveSphere p => S.cover q) := by
  have hval : IsLocalHomeomorph
      (Subtype.val : PuncturedProjectiveSphere p → UnitThreeSphere) :=
    (isOpen_puncturedProjectiveSphere p).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  exact S.local_diffeomorph.isLocalHomeomorphOn.comp
    hval.isLocalHomeomorphOn (fun q _ => q.property)

include S in
theorem isOpen_target : IsOpen U := by
  have he : range (fun q : PuncturedProjectiveSphere p => S.cover q) = U := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact (S.restrictedCover q).property
    · intro hy
      obtain ⟨q, hq, hqy⟩ := S.image_eq.symm.subset hy
      exact ⟨⟨q, hq⟩, hqy⟩
  rw [← he, ← image_univ]
  exact S.isLocalHomeomorph_domRestrict.isOpenMap _ isOpen_univ

theorem restrictedCover_isLocalHomeomorph : IsLocalHomeomorph S.restrictedCover := by
  apply IsLocalHomeomorph.of_comp (g := (Subtype.val : U → Q))
    S.isLocalHomeomorph_domRestrict S.isOpen_target.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact S.isLocalHomeomorph_domRestrict.continuous.subtype_mk _

theorem restrictedCover_isClosedMap : IsClosedMap S.restrictedCover := by
  have hquot := S.restrictedCover_isLocalHomeomorph.isOpenMap.isQuotientMap
    S.restrictedCover_isLocalHomeomorph.continuous S.restrictedCover_surjective
  intro A hA
  apply hquot.isClosed_preimage.mp
  have he : S.restrictedCover ⁻¹' (S.restrictedCover '' A) =
      A ∪ PuncturedProjectiveSphere.antipode ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rcases (S.restrictedCover_eq_iff y x).mp hyx with h | h
      · exact Or.inl (h ▸ hy)
      · right
        change PuncturedProjectiveSphere.antipode x ∈ A
        exact h ▸ hy
    · rintro (hx | hx)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨PuncturedProjectiveSphere.antipode x, hx,
          (S.restrictedCover_eq_iff _ _).mpr (Or.inr rfl)⟩
  rw [he]
  exact hA.union (hA.preimage (PuncturedProjectiveSphere.continuous_antipode p))

theorem restrictedCover_isCoveringMap : IsCoveringMap S.restrictedCover := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact S.restrictedCover_isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun y _ => S.restrictedCover_finite_fiber y)
    S.restrictedCover_isLocalHomeomorph.isLocalHomeomorphOn

theorem restrictedCover_isProperMap : IsProperMap S.restrictedCover :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨S.restrictedCover_isLocalHomeomorph.continuous, S.restrictedCover_isClosedMap,
      fun y => (S.restrictedCover_finite_fiber y).isCompact⟩

theorem isCompact_lift {K : Set Q} (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ K} := by
  have hKU' : K ⊆ range (Subtype.val : U → Q) := by simpa using hKU
  have hK' : IsCompact ((Subtype.val : U → Q) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK hKU'
  have hlift := (S.restrictedCover_isProperMap.isCompact_preimage hK').image
    (continuous_subtype_val : Continuous (Subtype.val : PuncturedProjectiveSphere p → UnitThreeSphere))
  convert hlift using 1
  ext q
  constructor
  · rintro ⟨hq, hqK⟩
    exact ⟨⟨q, hq⟩, hqK, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

end StandardPuncturedProjectiveCover

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

theorem CapCertificate.exists_projective_covering (C : CapCertificate g)
    (hkind : C.model_kind = .puncturedProjective) :
    ∃ S : StandardPuncturedProjectiveCover M C.puncture C.carrier,
      IsCoveringMap S.restrictedCover ∧ IsProperMap S.restrictedCover ∧
      IsCompact {q : UnitThreeSphere |
        Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.closed_core} := by
  obtain ⟨S⟩ := C.nonempty_projective_cover hkind
  exact ⟨S, S.restrictedCover_isCoveringMap, S.restrictedCover_isProperMap,
    S.isCompact_lift C.closed_core_compact C.closed_core_subset_carrier⟩

end PoincareConjecture
