import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Twist
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates
import Mathlib.Topology.Homotopy.Lifting









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => unitInterval

private instance : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩


noncomputable def cylinderIntegerTwist (n : ℤ) : (I × Circle) ≃ₜ (I × Circle) where
  toFun x := (x.1, x.2 + ((32 * (n : ℝ) * (x.1 : ℝ) : ℝ) : Circle))
  invFun x := (x.1, x.2 - ((32 * (n : ℝ) * (x.1 : ℝ) : ℝ) : Circle))
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem cylinderIntegerTwist_rim (n : ℤ) (x : I × Circle)
    (hx : x.1 = 0 ∨ x.1 = 1) : cylinderIntegerTwist n x = x := by
  have hn : ((32 * (n : ℝ) : ℝ) : Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨n, by simp [zsmul_eq_mul]; ring⟩
  apply Prod.ext
  · rfl
  · rcases hx with hx | hx <;> simp [cylinderIntegerTwist, hx, hn]



theorem exists_cylinder_winding_correction (f : C(I × Circle, I × Circle))
    (hzero : ∀ z, f (0, z) = (0, z)) (hone : ∀ z, f (1, z) = (1, z)) :
    ∃ n : ℤ, Nonempty ((f.comp
      ⟨cylinderIntegerTwist n, (cylinderIntegerTwist n).continuous⟩).HomotopyRel
        (ContinuousMap.id (I × Circle)) {x | x.1 = 0 ∨ x.1 = 1}) := by
  let error : C(I × Circle, Circle) := ⟨fun x => (f x).2 - x.2, by fun_prop⟩
  let zeroLift : C(Circle, ℝ) := ContinuousMap.const Circle 0
  have he0 (z : Circle) : error (0, z) = (zeroLift z : Circle) := by
    change (f (0, z)).2 - z = (0 : Circle)
    rw [hzero]
    simp
  let cov := AddCircle.isCoveringMap_coe (4 * (8 : ℝ))
  let lift := cov.liftHomotopy error zeroLift he0
  have hlift (x : I × Circle) : (lift x : Circle) = (f x).2 - x.2 :=
    congrFun (cov.liftHomotopy_lifts error zeroLift he0) x
  have hlift0 (z : Circle) : lift (0, z) = 0 :=
    cov.liftHomotopy_zero error zeroLift he0 z
  have hlift1 (z : Circle) : lift (1, z) = lift (1, 0) := by
    apply cov.const_of_comp (g := fun z : Circle => lift (1, z)) (by fun_prop) _ z 0
    intro z w
    rw [hlift, hlift, hone, hone]
    simp
  have htop : (lift (1, 0) : Circle) = 0 := by rw [hlift, hone]; simp
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mp htop
  have hn' (z : Circle) : lift (1, z) = 32 * (n : ℝ) := by
    rw [hlift1, ← hn]
    simp [zsmul_eq_mul]
    ring
  let shift : C(I × Circle, I × Circle) :=
    ⟨cylinderIntegerTwist (-n), (cylinderIntegerTwist (-n)).continuous⟩
  let g := f.comp shift
  let remaining : C(I × Circle, ℝ) :=
    ⟨fun x => lift (shift x) + 32 * ((-n : ℤ) : ℝ) * (x.1 : ℝ), by fun_prop⟩
  have hremaining (x : I × Circle) : (remaining x : Circle) = (g x).2 - x.2 := by
    change ((lift (shift x) + 32 * ((-n : ℤ) : ℝ) * (x.1 : ℝ) : ℝ) : Circle) = _
    rw [AddCircle.coe_add, hlift]
    change (f (shift x)).2 -
      (x.2 + ((32 * ((-n : ℤ) : ℝ) * (x.1 : ℝ) : ℝ) : Circle)) +
      ((32 * ((-n : ℤ) : ℝ) * (x.1 : ℝ) : ℝ) : Circle) = (f (shift x)).2 - x.2
    abel
  have hremRim (x : I × Circle) (hx : x.1 = 0 ∨ x.1 = 1) : remaining x = 0 := by
    change lift (shift x) + 32 * ((-n : ℤ) : ℝ) * (x.1 : ℝ) = 0
    rw [show shift x = x from cylinderIntegerTwist_rim (-n) x hx]
    rcases hx with hx | hx
    · rcases x with ⟨t, z⟩
      dsimp at hx ⊢
      subst t
      simp [hlift0]
    · rcases x with ⟨t, z⟩
      dsimp at hx ⊢
      subst t
      rw [hn']
      simp
  have hgRim (x : I × Circle) (hx : x.1 = 0 ∨ x.1 = 1) : g x = x := by
    change f (shift x) = x
    rw [show shift x = x from cylinderIntegerTwist_rim (-n) x hx]
    rcases x with ⟨t, z⟩
    rcases hx with hx | hx
    · change t = 0 at hx
      subst t
      exact hzero z
    · change t = 1 at hx
      subst t
      exact hone z
  refine ⟨-n, ⟨{
    toFun := fun z => (Icc.convexComb (g z.2).1 z.2.1 z.1,
      z.2.2 + (((1 - (z.1 : ℝ)) * remaining z.2 : ℝ) : Circle))
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro x
      apply Prod.ext
      · change Icc.convexComb (g x).1 x.1 0 = (g x).1
        simp
      · change x.2 + (((1 - (0 : ℝ)) * remaining x : ℝ) : Circle) = (g x).2
        simp only [sub_zero, one_mul, hremaining]
        abel
    map_one_left := by intro x; simp
    prop' := by
      intro t x hx
      change (Icc.convexComb (g x).1 x.1 t,
        x.2 + (((1 - (t : ℝ)) * remaining x : ℝ) : Circle)) = g x
      rw [hgRim x hx, hremRim x hx]
      simp }⟩⟩




theorem exists_annulus_winding_correction (f : C(Ann, I × Circle))
    (hrims : ∀ side z, f (annulusRimPoint side z) = (if side then 1 else 0, z)) :
    ∃ T : Ann ≃ₜ Ann, T.IsFinitePL ∧
      (∀ side z, T (annulusRimPoint side z) = annulusRimPoint side z) ∧
      Nonempty ((f.comp ⟨T, T.continuous⟩).HomotopyRel
        ⟨annulusCylinderHomeomorph.symm, annulusCylinderHomeomorph.symm.continuous⟩
        annulusRims) := by
  let C : C(I × Circle, Ann) :=
    ⟨annulusCylinderHomeomorph, annulusCylinderHomeomorph.continuous⟩
  obtain ⟨n, ⟨H⟩⟩ := exists_cylinder_winding_correction (f.comp C)
    (by
      intro z
      change f (annulusCylinderHomeomorph (0, z)) = (0, z)
      rw [annulusCylinderHomeomorph_zero, hrims]
      rfl)
    (by
      intro z
      change f (annulusCylinderHomeomorph (1, z)) = (1, z)
      rw [annulusCylinderHomeomorph_one, hrims]
      rfl)
  obtain ⟨T, hT, hTv, hTrims⟩ := exists_integer_annulus_twist n
  have hTC (x : Ann) : T x =
      annulusCylinderHomeomorph (cylinderIntegerTwist n (annulusCylinderHomeomorph.symm x)) := by
    obtain ⟨y, rfl⟩ := annulusCylinderHomeomorph.surjective x
    rw [annulusCylinderHomeomorph.symm_apply_apply]
    simp only [annulusCylinderHomeomorph_apply]
    change T (annulusRimCylinder y) =
      annulusRimCylinder (y.1, y.2 + ((32 * (n : ℝ) * (y.1 : ℝ) : ℝ) : Circle))
    exact hTv y.1 y.2
  refine ⟨T, hT, hTrims, ⟨{
    toFun := fun z => H (z.1, annulusCylinderHomeomorph.symm z.2)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro x
      rw [H.apply_zero]
      change f (annulusCylinderHomeomorph (cylinderIntegerTwist n
        (annulusCylinderHomeomorph.symm x))) = f (T x)
      rw [hTC]
    map_one_left := by intro x; exact H.apply_one _
    prop' := by
      intro t x hx
      have hr : (annulusCylinderHomeomorph.symm x).1 = 0 ∨
          (annulusCylinderHomeomorph.symm x).1 = 1 := by
        apply (annulusCylinderHomeomorph_mem_rims _).mp
        rwa [annulusCylinderHomeomorph.apply_symm_apply]
      change H (t, annulusCylinderHomeomorph.symm x) = f (T x)
      rw [H.eq_fst t hr]
      change f (annulusCylinderHomeomorph (cylinderIntegerTwist n
        (annulusCylinderHomeomorph.symm x))) = f (T x)
      rw [hTC] }⟩⟩

end PoincareConjecture.M76.Dehn
