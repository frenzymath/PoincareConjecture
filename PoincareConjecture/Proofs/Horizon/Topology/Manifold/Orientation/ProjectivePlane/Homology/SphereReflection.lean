import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Homology.OpenCoverSwap
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereOpenCover
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional











set_option autoImplicit false

noncomputable section

open Set Metric CategoryTheory HomologicalComplex
open scoped Topology unitInterval

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]



def sphereIsometryMap (R : E ≃ₗᵢ[Real] E) : C(sphere (0 : E) 1, sphere (0 : E) 1) := by
  have hR (x : sphere (0 : E) 1) : R x.val ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, R.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.property
  exact ⟨fun x => ⟨R x.val, hR x⟩,
    (R.continuous.comp continuous_subtype_val).subtype_mk hR⟩



def poleReflection (p : sphere (0 : E) 1) : E ≃ₗᵢ[Real] E :=
  (Real ∙ p.val)ᗮ.reflection

omit [FiniteDimensional Real E] in


@[simp]
theorem poleReflection_pole (p : sphere (0 : E) 1) : poleReflection p p.val = -p.val :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg p.val

omit [FiniteDimensional Real E] in


theorem poleReflection_mapsTo (p : sphere (0 : E) 1) :
    MapsTo (sphereIsometryMap (poleReflection p)) ({p}ᶜ : Set (sphere (0 : E) 1))
      ({-p}ᶜ : Set (sphere (0 : E) 1)) := by
  intro x hx he
  apply hx
  apply Subtype.ext
  apply (poleReflection p).injective
  exact (congrArg Subtype.val he).trans (poleReflection_pole p).symm

omit [FiniteDimensional Real E] in


theorem poleReflection_mapsTo_reverse (p : sphere (0 : E) 1) :
    MapsTo (sphereIsometryMap (poleReflection p)) ({-p}ᶜ : Set (sphere (0 : E) 1))
      ({p}ᶜ : Set (sphere (0 : E) 1)) := by
  intro x hx he
  apply hx
  apply Subtype.ext
  apply (poleReflection p).injective
  have hRneg : (poleReflection p) ((-p : sphere (0 : E) 1).val) = p.val := by
    rw [coe_neg_sphere, map_neg, poleReflection_pole, neg_neg]
  exact (congrArg Subtype.val he).trans hRneg.symm

omit [FiniteDimensional Real E] in


theorem equatorialProjection_ne_zero_iff (p x : sphere (0 : E) 1) :
    (Real ∙ p.val)ᗮ.starProjection x.val ≠ 0 ↔ x ≠ p ∧ x ≠ -p := by
  constructor
  · intro h
    constructor
    · rintro rfl
      exact h (Submodule.starProjection_orthogonalComplement_singleton_eq_zero _)
    · rintro rfl
      apply h
      simp only [coe_neg_sphere, map_neg,
        Submodule.starProjection_orthogonalComplement_singleton_eq_zero, neg_zero]
  · rintro ⟨hx, hx'⟩ hzero
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at hzero
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzero
    have hn : |a| = 1 := by
      have hn := congrArg norm ha
      simpa only [norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp p.property,
        mem_sphere_zero_iff_norm.mp x.property, mul_one] using hn
    by_cases ha0 : 0 ≤ a
    · have ha1 : a = 1 := by simpa only [abs_of_nonneg ha0] using hn
      apply hx
      apply Subtype.ext
      simpa only [ha1, one_smul] using ha.symm
    · have ha1 : a = -1 := by rw [abs_of_neg (lt_of_not_ge ha0)] at hn; linarith
      apply hx'
      apply Subtype.ext
      simpa only [ha1, neg_one_smul, coe_neg_sphere] using ha.symm

omit [FiniteDimensional Real E] in



theorem sphereReflection_overlap_homotopic (p : sphere (0 : E) 1) :
    (ContinuousMap.id (↥(({p}ᶜ : Set (sphere (0 : E) 1)) ∩ {-p}ᶜ))).Homotopic
      (coverIntersectionMap {p}ᶜ {-p}ᶜ (sphereIsometryMap (poleReflection p))
        (poleReflection_mapsTo p) (poleReflection_mapsTo_reverse p)) := by
  let K : Submodule Real E := (Real ∙ p.val)ᗮ
  let U : Set (sphere (0 : E) 1) := {p}ᶜ ∩ {-p}ᶜ
  let R := poleReflection p
  have hPP (x : E) : K.starProjection (K.starProjection x) = K.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (K.orthogonalProjectionOnto x).property
  have hPR (x : E) : K.starProjection (R x) = K.starProjection x := by
    change K.starProjection (2 • K.starProjection x - x) = _
    rw [map_sub, map_nsmul, hPP]
    simp [two_smul]
  let v (z : unitInterval × U) : E :=
    (1 - (z.1 : Real)) • z.2.val.val + (z.1 : Real) • R z.2.val.val
  have hPv (z : unitInterval × U) : K.starProjection (v z) = K.starProjection z.2.val.val := by
    simp only [v, map_add, map_smul, hPR]
    rw [← add_smul]
    simp
  have hPx (x : U) : K.starProjection x.val.val ≠ 0 :=
    (equatorialProjection_ne_zero_iff p x.val).mpr x.property
  have hv (z : unitInterval × U) : v z ≠ 0 := by
    intro he
    apply hPx z.2
    rw [← hPv z, he, map_zero]
  have hn (z : unitInterval × U) : ‖v z‖ ≠ 0 := norm_ne_zero_iff.mpr (hv z)
  let q (z : unitInterval × U) : sphere (0 : E) 1 :=
    ⟨‖v z‖⁻¹ • v z, by simp [norm_smul, hn z]⟩
  have hq (z : unitInterval × U) : q z ∈ U := by
    apply (equatorialProjection_ne_zero_iff p (q z)).mp
    change K.starProjection (‖v z‖⁻¹ • v z) ≠ 0
    rw [map_smul, hPv]
    exact smul_ne_zero (inv_ne_zero (hn z)) (hPx z.2)
  have hvcont : Continuous v := by dsimp [v]; fun_prop
  refine ⟨{
    toFun := fun z => ⟨q z, hq z⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · exact (((hvcont.norm.inv₀ hn).smul hvcont).subtype_mk _).subtype_mk _
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    change ‖v (0, x)‖⁻¹ • v (0, x) = x.val.val
    simp [v, mem_sphere_zero_iff_norm.mp x.val.property]
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    change ‖v (1, x)‖⁻¹ • v (1, x) = R x.val.val
    simp [v, R.norm_map, mem_sphere_zero_iff_norm.mp x.val.property]

end Poincare.Topology.Orientation.ProjectivePlane
