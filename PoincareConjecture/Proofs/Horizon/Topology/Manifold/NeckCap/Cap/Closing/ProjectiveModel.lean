import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.Covering
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.LocalAtTarget











noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

private theorem projectiveThreeProjection_isOpenMap :
    IsOpenMap (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  have hs : (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹'
      (Quotient.mk' '' U) = U ∪ Neg.neg ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases Quotient.exact hxy with hxy | hxy
      · exact Or.inl (hxy ▸ hy)
      · right
        change -x ∈ U
        exact hxy ▸ hy
    · rintro (hx | hx)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨-x, hx, Quotient.sound (Or.inr rfl)⟩
  rw [hs]
  exact hU.union (hU.preimage continuous_neg)

namespace StandardProjectiveSmoothCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]



def homeomorph (S : StandardProjectiveSmoothCover Q) : Q ≃ₜ RealProjectiveThree := by
  let f : C(UnitThreeSphere, Q) := ⟨S.cover, S.local_diffeomorph.contMDiff.continuous⟩
  have hf : IsQuotientMap f := S.local_diffeomorph.isLocalHomeomorph.isOpenMap.isQuotientMap
    f.continuous S.surjective
  exact hf.homeomorph.symm.trans (Homeomorph.Quotient.congrRight S.fibers)

end StandardProjectiveSmoothCover

namespace StandardPuncturedProjectiveCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}



def homeomorph (S : StandardPuncturedProjectiveCover Q p U) :
    U ≃ₜ PuncturedRealProjectiveThree p := by
  let f : C(PuncturedProjectiveSphere p, U) :=
    ⟨S.restrictedCover, S.restrictedCover_isLocalHomeomorph.continuous⟩
  let q : C(PuncturedProjectiveSphere p, PuncturedRealProjectiveThree p) :=
    ⟨fun x => ⟨Quotient.mk' x.val, x.property⟩,
      (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _⟩
  have hf : IsQuotientMap f := S.restrictedCover_isLocalHomeomorph.isOpenMap.isQuotientMap
    f.continuous S.restrictedCover_surjective
  have hq : IsQuotientMap q := by
    have h : IsOpenQuotientMap (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) :=
      ⟨Quotient.mk'_surjective, continuous_quotient_mk', projectiveThreeProjection_isOpenMap⟩
    exact (h.restrictPreimage {x | x ≠ p}).isQuotientMap
  have hrel : ∀ x y : PuncturedProjectiveSphere p,
      Setoid.ker f x y ↔ Setoid.ker q x y := by
    intro x y
    change S.restrictedCover x = S.restrictedCover y ↔ q x = q y
    simp only [Subtype.ext_iff]
    change S.cover x.val = S.cover y.val ↔ Quotient.mk' x.val = Quotient.mk' y.val
    exact (S.fibers x y x.property y.property).trans
      (@Quotient.eq UnitThreeSphere realProjectiveThreeSetoid x.val y.val).symm
  exact hf.homeomorph.symm.trans ((Homeomorph.Quotient.congrRight hrel).trans hq.homeomorph)

end StandardPuncturedProjectiveCover

namespace SmoothProjectiveDoubleModel

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [T2Space Q]



def sphereHomeomorph (D : SmoothProjectiveDoubleModel Q) : D.sphere ≃ₜ UnitTwoSphere := by
  have hzero (x : UnitTwoSphere) : (x, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 :=
    ⟨mem_univ _, by norm_num⟩
  let f : UnitTwoSphere → D.sphere := fun x =>
    ⟨D.collar (x, 0), D.collar_sphere.subset ⟨(x, 0), ⟨mem_univ _, rfl⟩, rfl⟩⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc : ContinuousAt D.collar (x, (0 : ℝ)) :=
      (D.collar_local_diffeomorph ⟨(x, 0), hzero x⟩).contMDiffAt.continuousAt
    exact hc.comp (f := fun z : UnitTwoSphere => (z, (0 : ℝ)))
      (continuous_id.prodMk continuous_const).continuousAt
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact congrArg Prod.fst (D.collar_injective (hzero x) (hzero y)
        (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨⟨x, t⟩, ⟨_, ht⟩, hxy⟩ := D.collar_sphere.symm.subset y.property
      have ht' : t = 0 := ht
      subst t
      exact ⟨x, Subtype.ext hxy⟩
  exact ((Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed hf hf.isClosedMap).symm



def connectedSumModel (D : SmoothProjectiveDoubleModel Q) :
    RealProjectiveThreeConnectedSumModel Q inferInstance := by
  have hfirst : (D.first_region ∪ D.sphere) \ D.sphere = D.first_region := by
    ext x
    constructor
    · rintro ⟨hx | hx, hs⟩
      · exact hx
      · exact (hs hx).elim
    · intro hx
      exact ⟨Or.inl hx, fun hs => Set.disjoint_left.mp D.sphere_disjoint hs (Or.inl hx)⟩
  have hsecond : (D.second_region ∪ D.sphere) \ D.sphere = D.second_region := by
    ext x
    constructor
    · rintro ⟨hx | hx, hs⟩
      · exact hx
      · exact (hs hx).elim
    · intro hx
      exact ⟨Or.inl hx, fun hs => Set.disjoint_left.mp D.sphere_disjoint hs (Or.inr hx)⟩
  refine
    { sphere := D.sphere
      sphere_model := D.sphereHomeomorph
      first_piece := D.first_region ∪ D.sphere
      second_piece := D.second_region ∪ D.sphere
      union_eq := ?_
      intersection_eq := ?_
      first_puncture := D.first_puncture
      second_puncture := D.second_puncture
      first_piece_model := (Homeomorph.setCongr hfirst).trans D.first_model.homeomorph
      second_piece_model := (Homeomorph.setCongr hsecond).trans D.second_model.homeomorph }
  · rw [union_union_union_comm, union_self, D.cover]
  · ext x
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact (Set.disjoint_left.mp D.disjoint hx hy).elim
      · exact hy
      · exact hx
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩

end SmoothProjectiveDoubleModel

end PoincareConjecture
