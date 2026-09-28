import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralCompactGluing
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSupportLocalization
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Set

universe u

namespace Poincare.Topology

theorem integralSupportHomology_coefficient_locallyConstant
    {X : Type u} [TopologicalSpace X] [T2Space X] (d : Nat)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) d)
    (basis : ∀ x : X, Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) d)
    (hbasis : ∀ x, basis x 1 = omega x)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U d,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d b = omega y)
    (a : integralSupportHomology (univ : Set X) d) :
    IsLocallyConstant (fun x : X => (basis x).symm
      (integralSupportHomologyRestriction (subset_univ ({x} : Set X)) d a)) := by
  let coefficient (x : X) : Int := (basis x).symm
    (integralSupportHomologyRestriction (subset_univ ({x} : Set X)) d a)
  have hvalue (x : X) (z : Int) : basis x z = z • omega x := by
    simpa only [zsmul_eq_mul, Int.cast_id, mul_one, hbasis] using map_zsmul (basis x) z 1
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨U, hU, hxU, b, hb⟩ := hlocal x
  let c : integralSupportHomology U d :=
    integralSupportHomologyRestriction (subset_univ U) d a - coefficient x • b
  have hc : integralSupportHomologyRestriction (singleton_subset_iff.mpr hxU) d c = 0 := by
    dsimp only [c]
    rw [map_sub, map_zsmul, integralSupportHomologyRestriction_apply_comp, hb x hxU]
    rw [← hvalue]
    exact sub_eq_zero.mpr ((basis x).apply_symm_apply _).symm
  obtain ⟨V, hV, hxV, hcV⟩ :=
    exists_open_integralRelativeHomology_restriction_eq_zero U d c x hxU hc
  change integralSupportHomologyRestriction (inter_subset_left : U ∩ V ⊆ U) d c = 0 at hcV
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro y hy
  have hyc : integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1) d c = 0 := by
    have h := congrArg (fun z => integralSupportHomologyRestriction
      (singleton_subset_iff.mpr hy) d z) hcV
    rw [map_zero, integralSupportHomologyRestriction_apply_comp] at h
    exact h
  dsimp only [c] at hyc
  rw [map_sub, map_zsmul, integralSupportHomologyRestriction_apply_comp, hb y hy.1,
    sub_eq_zero] at hyc
  apply (basis y).injective
  rw [(basis y).apply_symm_apply, hvalue]
  exact hyc

theorem nonempty_integralSupportHomologyUniv_equiv_int
    {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    [CompactSpace X] [PreconnectedSpace X] (x0 : X) (d : Nat)
    (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L d)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) d)
    (hgen : ∀ x : X, ∃ b : Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) d,
      b 1 = omega x)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U d,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d b = omega y) :
    Nonempty (integralSupportHomology (univ : Set X) d ≃ₗ[Int] Int) := by
  classical
  choose basis hbasis using hgen
  let coefficient (a : integralSupportHomology (univ : Set X) d) (x : X) : Int :=
    (basis x).symm (integralSupportHomologyRestriction (subset_univ ({x} : Set X)) d a)
  have hconstant (a : integralSupportHomology (univ : Set X) d) (x y : X) :
      coefficient a x = coefficient a y :=
    (integralSupportHomology_coefficient_locallyConstant d omega basis hbasis hlocal
      a).apply_eq_of_preconnectedSpace x y
  let F : integralSupportHomology (univ : Set X) d →ₗ[Int] Int :=
    (basis x0).symm.toLinearMap.comp
      (integralSupportHomologyRestriction (subset_univ ({x0} : Set X)) d).hom
  have hF (a : integralSupportHomology (univ : Set X) d) : F a = coefficient a x0 := rfl
  have hinj : Function.Injective F := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hD univ isCompact_univ
    intro x hx
    have hzero : F (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hc : coefficient (a - b) x = 0 :=
      (hconstant (a - b) x x0).trans hzero
    apply (basis x).symm.injective
    rw [map_zero]
    exact hc
  obtain ⟨fundamental, hfundamental, _⟩ :=
    exists_unique_integralSupportHomology_compact_gluing d hD omega univ isCompact_univ
      (fun x _ => hlocal x)
  have hfundamentalF : F fundamental = 1 := by
    change (basis x0).symm
      (integralSupportHomologyRestriction (subset_univ ({x0} : Set X)) d fundamental) = 1
    rw [hfundamental x0 (mem_univ x0), ← hbasis x0, LinearEquiv.symm_apply_apply]
  have hsurj : Function.Surjective F := by
    intro z
    refine ⟨z • fundamental, ?_⟩
    rw [map_zsmul, hfundamentalF, zsmul_eq_mul, mul_one, Int.cast_id]
  exact ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩⟩

end Poincare.Topology
