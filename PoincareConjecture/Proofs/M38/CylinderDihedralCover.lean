import PoincareConjecture.Proofs.M38.ProjectiveReflectionCover
import PoincareConjecture.Proofs.M38.DihedralCutComponents
import Mathlib.GroupTheory.SpecificGroups.Dihedral










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38


noncomputable def cylinderDihedralHeight : ZMod 0 →+* ℝ := ZMod.castHom (dvd_refl 0) ℝ


@[instance_reducible]
noncomputable def cylinderDihedralAction : MulAction (DihedralGroup 0) RoundCylinderSpace where
  smul g p := match g with
    | .r n => (p.1, p.2 + cylinderDihedralHeight n)
    | .sr n => (-p.1, -cylinderDihedralHeight n - p.2)
  one_smul p := by
    change (p.1, p.2 + cylinderDihedralHeight 0) = p
    simp
  mul_smul g h p := by
    cases g with
    | r n =>
      cases h with
      | r m =>
        change (p.1, p.2 + cylinderDihedralHeight (n + m)) =
          (p.1, p.2 + cylinderDihedralHeight m + cylinderDihedralHeight n)
        congr 1
        rw [map_add]
        ring
      | sr m =>
        change (-p.1, -cylinderDihedralHeight (m - n) - p.2) =
          (-p.1, -cylinderDihedralHeight m - p.2 + cylinderDihedralHeight n)
        congr 1
        rw [map_sub]
        ring
    | sr n =>
      cases h with
      | r m =>
        change (-p.1, -cylinderDihedralHeight (n + m) - p.2) =
          (-p.1, -cylinderDihedralHeight n - (p.2 + cylinderDihedralHeight m))
        congr 1
        rw [map_add]
        ring
      | sr m =>
        change (p.1, p.2 + cylinderDihedralHeight (m - n)) =
          (- -p.1, -cylinderDihedralHeight n - (-cylinderDihedralHeight m - p.2))
        rw [neg_neg]
        congr 1
        rw [map_sub]
        ring

attribute [local instance] cylinderDihedralAction


theorem cylinderDihedral_rotation (n : ℤ) (p : RoundCylinderSpace) :
    (DihedralGroup.r (n : ZMod 0) : DihedralGroup 0) • p = cylinderIntegerTranslation n p := rfl


theorem cylinderDihedral_reflection (n : ℤ) (p : RoundCylinderSpace) :
    (DihedralGroup.sr (n : ZMod 0) : DihedralGroup 0) • p = cylinderIntegerReflection (-n) p := by
  apply Prod.ext
  · rfl
  · change -(n : ℝ) - p.2 = ((-n : ℤ) : ℝ) - p.2
    rw [Int.cast_neg]


instance cylinderDihedral_continuous : ContinuousConstSMul (DihedralGroup 0) RoundCylinderSpace where
  continuous_const_smul g := by
    cases g with
    | r n => exact continuous_fst.prodMk (continuous_snd.add continuous_const)
    | sr n =>
      exact (continuous_neg.comp continuous_fst).prodMk (continuous_const.sub continuous_snd)


theorem cylinderDihedral_free (g : DihedralGroup 0) (p : RoundCylinderSpace)
    (h : g • p = p) : g = 1 := by
  cases g with
  | r n =>
    have ht := congrArg Prod.snd h
    change p.2 + cylinderDihedralHeight n = p.2 at ht
    have hn : n = 0 := (ZMod.castHom_injective ℝ)
      (show cylinderDihedralHeight n = cylinderDihedralHeight 0 by rw [map_zero]; linarith)
    simpa only [hn] using (DihedralGroup.r_zero (n := 0))
  | sr n =>
    have hz := congrArg Prod.fst h
    change -p.1 = p.1 at hz
    have hpair : (-p.1, -(0 : ℝ)) = (p.1, (0 : ℝ)) := by simp only [hz, neg_zero]
    exact False.elim (cylinderReflection_ne (p.1, 0) hpair)



theorem cylinderDihedral_isQuotientCoveringMap
    {Q : GeneralizedSliceCarrier.{u}} (q : RoundCylinderSpace → Q.carrier)
    (hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (hsurj : Function.Surjective q)
    (hfibers : ∀ x y, q x = q y ↔
      ∃ n : ℤ, x = cylinderIntegerTranslation n y ∨ x = cylinderIntegerReflection n y) :
    IsQuotientCoveringMap q (DihedralGroup 0) := by
  have horbit (x y : RoundCylinderSpace) : q x = q y ↔ x ∈ MulAction.orbit (DihedralGroup 0) y := by
    rw [hfibers]
    constructor
    · rintro ⟨n, h | h⟩
      · exact ⟨DihedralGroup.r (n : ZMod 0), (cylinderDihedral_rotation n y).trans h.symm⟩
      · refine ⟨DihedralGroup.sr ((-n : ℤ) : ZMod 0), ?_⟩
        have he : cylinderIntegerReflection (- -n) y = cylinderIntegerReflection n y := by
          rw [neg_neg]
        exact (cylinderDihedral_reflection (-n) y).trans (he.trans h.symm)
    · rintro ⟨g, hg⟩
      cases g with
      | r n =>
        obtain ⟨m, rfl⟩ := ZMod.intCast_surjective n
        exact ⟨m, Or.inl (hg.symm.trans (cylinderDihedral_rotation m y))⟩
      | sr n =>
        obtain ⟨m, rfl⟩ := ZMod.intCast_surjective n
        exact ⟨-m, Or.inr (hg.symm.trans (cylinderDihedral_reflection m y))⟩
  refine {
    toIsQuotientMap :=
      hq.isLocalHomeomorph.isOpenMap.isQuotientMap hq.contMDiff.continuous hsurj
    apply_eq_iff_mem_orbit := horbit _ _
    disjoint := ?_ }
  intro p
  let h := hq p
  refine ⟨h.localInverse.target, h.localInverse.open_target.mem_nhds h.localInverse_mem_target, ?_⟩
  intro g hg
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := hg
  have he : q (g • y) = q y := (horbit _ _).mpr ⟨g, rfl⟩
  apply cylinderDihedral_free g y
  calc
    g • y = h.localInverse (q (g • y)) := (h.localInverse_left_inv hx).symm
    _ = h.localInverse (q y) := congrArg h.localInverse he
    _ = y := h.localInverse_left_inv hy

end PoincareConjecture.M38
