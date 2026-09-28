import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Twist
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.DepthHalves

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => unitInterval

noncomputable def annularIntegerTwist (n : ℤ) : Ann ≃ₜ Ann :=
  (exists_integer_annulus_twist n).choose

theorem annularIntegerTwist_finitePL (n : ℤ) : (annularIntegerTwist n).IsFinitePL :=
  (exists_integer_annulus_twist n).choose_spec.1

theorem annularIntegerTwist_symm_finitePL (n : ℤ) :
    (annularIntegerTwist n).symm.IsFinitePL := (annularIntegerTwist_finitePL n).symm

theorem annularIntegerTwist_cylinder (n : ℤ) (t : I) (z : Circle) :
    annularIntegerTwist n (annulusCylinderHomeomorph (t, z)) =
      annulusCylinderHomeomorph (t, z + ((32 * (n : ℝ) * (t : ℝ) : ℝ) : Circle)) := by
  simp only [annulusCylinderHomeomorph_apply]
  exact (exists_integer_annulus_twist n).choose_spec.2.1 t z

theorem annularIntegerTwist_symm_cylinder (n : ℤ) (t : I) (z : Circle) :
    (annularIntegerTwist n).symm (annulusCylinderHomeomorph (t, z)) =
      annulusCylinderHomeomorph (t, z - ((32 * (n : ℝ) * (t : ℝ) : ℝ) : Circle)) := by
  apply (annularIntegerTwist n).injective
  rw [Homeomorph.apply_symm_apply, annularIntegerTwist_cylinder, sub_add_cancel]

theorem annularIntegerTwist_rim (n : ℤ) (b : Bool) (z : Circle) :
    annularIntegerTwist n (annulusRimPoint b z) = annulusRimPoint b z :=
  (exists_integer_annulus_twist n).choose_spec.2.2 b z

theorem annularIntegerTwist_core (n : ℤ) (z : Circle) :
    annularIntegerTwist n (annulusCoreCircle z) =
      annulusCoreCircle (z + ((16 * (n : ℝ) : ℝ) : Circle)) := by
  change annularIntegerTwist n (annulusCylinderHomeomorph (⟨1 / 2, by norm_num⟩, z)) = _
  rw [annularIntegerTwist_cylinder]
  change annulusCylinderHomeomorph (⟨1 / 2, by norm_num⟩,
    z + ((32 * (n : ℝ) * (1 / 2) : ℝ) : Circle)) = _
  rw [show 32 * (n : ℝ) * (1 / 2) = 16 * n by ring]
  rfl

theorem annularIntegerTwist_core_image (n : ℤ) :
    annularIntegerTwist n '' range annulusCoreCircle = range annulusCoreCircle := by
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, (annularIntegerTwist_core n z).symm⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨annulusCoreCircle (z - ((16 * (n : ℝ) : ℝ) : Circle)), mem_range_self _, ?_⟩
    rw [annularIntegerTwist_core, sub_add_cancel]

noncomputable def annularTwistRadialLift (n : ℤ) : C(I, ℝ) :=
  ⟨fun t => 32 * (n : ℝ) * (t : ℝ), by fun_prop⟩

theorem annularTwistRadialLift_zero (n : ℤ) : annularTwistRadialLift n 0 = 0 := by
  simp [annularTwistRadialLift]

theorem annularTwistRadialLift_one (n : ℤ) : annularTwistRadialLift n 1 = 32 * (n : ℝ) := by
  simp [annularTwistRadialLift]

theorem annularTwistRadialLift_formula (n : ℤ) (t : I) :
    ((annularTwistRadialLift n t : ℝ) : Circle) =
      (annulusCylinderHomeomorph.symm
        (annularIntegerTwist n (annulusCylinderHomeomorph (t, 0)))).2 := by
  rw [annularIntegerTwist_cylinder, annulusCylinderHomeomorph.symm_apply_apply, zero_add]
  rfl

theorem exists_finitePL_annularTwist_radial_arc (n : ℤ) :
    ∃ a : ℝ → P2, FinitePiecewiseAffineOn a (Icc (0 : ℝ) 1) ∧
      InjOn a (Icc (0 : ℝ) 1) ∧
      (∀ t : I, a t = (annularIntegerTwist n (annulusCylinderHomeomorph (t, 0)) : P2)) ∧
      a 0 = (annulusRimPoint false 0 : P2) ∧ a 1 = (annulusRimPoint true 0 : P2) := by
  let d : ℝ →ᴬ[ℝ] P2 := (ContinuousAffineMap.const ℝ ℝ 0).prod
    ((2 : ℝ) • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ 1)
  have hd (t : ℝ) : d t = (0, 2 * t - 1) := rfl
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hdPL : FinitePiecewiseAffineOn d (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine d⟩
  let r : ℝ → P2 := wrappedStripMap 8 ∘ d
  have hr : FinitePiecewiseAffineOn r (Icc (0 : ℝ) 1) :=
    (finitePiecewiseAffineOn_wrappedStripMap (L := 8) (d := 1)
      (by norm_num) (by norm_num)).comp hdPL (by
        intro t ht
        rw [hd]
        exact ⟨⟨le_rfl, by norm_num⟩, by constructor <;> linarith [ht.1, ht.2]⟩)
  have hrval (t : I) : r t = (annulusCylinderHomeomorph (t, 0) : P2) := by
    rw [annulusCylinderHomeomorph_apply]
    change wrappedStripMap 8 (0, 2 * (t : ℝ) - 1) =
      annulusMap 8 (by norm_num) (0, 2 * (t : ℝ) - 1)
    exact (annulusMap_coe (s := 0) (by norm_num)
      (by have h : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr
            ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
          linarith)
      (by constructor <;> norm_num)).symm
  obtain ⟨f, hf, hfv⟩ := annularIntegerTwist_finitePL n
  have hrmem : MapsTo r (Icc (0 : ℝ) 1) Ann := by
    intro t ht
    rw [hrval ⟨t, ht⟩]
    exact (annulusCylinderHomeomorph (⟨t, ht⟩, 0)).property
  have hvalue (t : I) : (f ∘ r) t =
      (annularIntegerTwist n (annulusCylinderHomeomorph (t, 0)) : P2) := by
    rw [Function.comp_apply, hrval, ← hfv]
  refine ⟨f ∘ r, hf.comp hr hrmem, ?_, hvalue, ?_, ?_⟩
  · intro s hs t ht hst
    rw [hvalue ⟨s, hs⟩, hvalue ⟨t, ht⟩] at hst
    have h := annulusCylinderHomeomorph.injective
      ((annularIntegerTwist n).injective (Subtype.ext hst))
    exact congrArg (fun z : I × Circle => (z.1 : ℝ)) h
  · change (f ∘ r) ((0 : I) : ℝ) = _
    rw [hvalue 0, annulusCylinderHomeomorph_zero, annularIntegerTwist_rim]
  · change (f ∘ r) ((1 : I) : ℝ) = _
    rw [hvalue 1, annulusCylinderHomeomorph_one, annularIntegerTwist_rim]

end PoincareConjecture.M76.Dehn
