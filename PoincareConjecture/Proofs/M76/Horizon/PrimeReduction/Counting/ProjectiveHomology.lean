import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.AntipodalCoverHomology
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.ProjectiveDouble.Monodromy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.InvolutionQuotient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set CategoryTheory Limits
open scoped Topology

namespace PoincareConjecture.M76.ProjectiveHomology

abbrev quotientMap : UnitThreeSphere → RealProjectiveThree := Quotient.mk'

theorem quotientMap_isCoveringMap : IsCoveringMap quotientMap := by
  have hl := Poincare.Topology.Orientation.ProjectivePlane.involutionQuotient_isLocalHomeomorph
    realProjectiveThreeSetoid (Homeomorph.neg UnitThreeSphere) neg_neg
    (ne_neg_of_mem_unit_sphere ℝ) (fun _ _ => Iff.rfl)
  have hc : IsClosedMap quotientMap := by
    intro A hA
    apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
    have he : quotientMap ⁻¹' (quotientMap '' A) = A ∪ Neg.neg ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        rcases Quotient.eq.mp he with he | he
        · exact Or.inl (he ▸ hy)
        · exact Or.inr (by change -x ∈ A; exact he ▸ hy)
      · rintro (h | h)
        · exact ⟨x, h, rfl⟩
        · exact ⟨-x, h, Quotient.sound (Or.inr rfl)⟩
    rw [he]
    exact hA.union (hA.preimage continuous_neg)
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hc.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y _
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective y
    have he : quotientMap ⁻¹' {quotientMap a} = {a, -a} := by
      ext x
      exact Quotient.eq
    change (quotientMap ⁻¹' {quotientMap a}).Finite
    rw [he]
    exact (finite_singleton _).insert _
  · rw [preimage_univ]
    change IsLocalHomeomorphOn (Quotient.mk realProjectiveThreeSetoid) univ
    exact hl.isLocalHomeomorphOn

def puncturedMap (p : RealProjectiveThree) :
    PuncturedProjectiveSphere p → PuncturedRealProjectiveThree p :=
  fun x => ⟨quotientMap x, x.property⟩

def puncturedAntipode (p : RealProjectiveThree) :
    PuncturedProjectiveSphere p ≃ₜ PuncturedProjectiveSphere p where
  toFun := PuncturedProjectiveSphere.antipode
  invFun := PuncturedProjectiveSphere.antipode
  left_inv := PuncturedProjectiveSphere.antipode_antipode
  right_inv := PuncturedProjectiveSphere.antipode_antipode
  continuous_toFun := PuncturedProjectiveSphere.continuous_antipode p
  continuous_invFun := PuncturedProjectiveSphere.continuous_antipode p

theorem puncturedMap_isCoveringMap (p : RealProjectiveThree) :
    IsCoveringMap (puncturedMap p) :=
  (quotientMap_isCoveringMap.isCoveringMapOn.mono
    (subset_univ {x | x ≠ p})).isCoveringMap_restrictPreimage

theorem puncturedMap_surjective (p : RealProjectiveThree) :
    Function.Surjective (puncturedMap p) := by
  intro x
  obtain ⟨a, ha⟩ := Quotient.mk_surjective x.val
  exact ⟨⟨a, fun h => x.property (ha.symm.trans h)⟩, Subtype.ext ha⟩

theorem puncturedMap_fibers (p : RealProjectiveThree) (a b : PuncturedProjectiveSphere p) :
    puncturedMap p a = puncturedMap p b ↔ a = b ∨ a = puncturedAntipode p b := by
  rw [Subtype.ext_iff]
  change quotientMap a.val = quotientMap b.val ↔ _
  rw [show quotientMap a.val = quotientMap b.val ↔ a.val = b.val ∨ a.val = -b.val
    from Quotient.eq]
  simp only [Subtype.ext_iff]
  rfl

theorem punctured_exists_homology_retract (p : RealProjectiveThree)
    (R : ModuleCat (ZMod 2)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj (TopCat.of (PuncturedRealProjectiveThree p))).homology R 1)
      (r : (TopCat.toSSet.obj (TopCat.of (PuncturedRealProjectiveThree p))).homology R 1 ⟶ R),
      i ≫ r = 𝟙 R := by
  letI := PuncturedProjectiveSphere.pathConnectedSpace p
  let a : PuncturedProjectiveSphere p := Classical.arbitrary _
  exact AntipodalCover.exists_homology_retract (puncturedMap p) (puncturedAntipode p)
    PuncturedProjectiveSphere.antipode_antipode
    (fun z => (PuncturedProjectiveSphere.ne_antipode z).symm)
    (puncturedMap_fibers p) (puncturedMap_isCoveringMap p) (puncturedMap_surjective p)
    R a (PathConnectedSpace.somePath a (puncturedAntipode p a))

end PoincareConjecture.M76.ProjectiveHomology
