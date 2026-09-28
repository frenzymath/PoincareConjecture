import PoincareConjecture.Proofs.M38.DihedralCutComponents
import PoincareConjecture.Proofs.M38.MatchingCoverComparison











set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

private instance sphereDimension : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩


noncomputable def cylinderReflectionCenterShift (n : ℤ) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun p := (p.1, p.2 - (n : ℝ) / 2)
  invFun p := (p.1, p.2 + (n : ℝ) / 2)
  left_inv _p := Prod.ext rfl (sub_add_cancel _ _)
  right_inv _p := Prod.ext rfl (add_sub_cancel_right _ _)
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)


theorem cylinderReflectionCenterShift_reflection (n : ℤ) (p : RoundCylinderSpace) :
    cylinderReflectionCenterShift n (cylinderIntegerReflection n p) =
      (-(cylinderReflectionCenterShift n p).1, -(cylinderReflectionCenterShift n p).2) := by
  apply Prod.ext
  · rfl
  · change (n : ℝ) - p.2 - (n : ℝ) / 2 = -(p.2 - (n : ℝ) / 2)
    ring


theorem centeredProjectivePolar_fibers
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (n : ℤ) (x y : RoundCylinderSpace) :
    projectivePolarMap.{u} L (cylinderReflectionCenterShift n x) =
        projectivePolarMap L (cylinderReflectionCenterShift n y) ↔
      x = y ∨ x = cylinderIntegerReflection n y := by
  have hinj : Function.Injective (cylinderReflectionCenterShift n) :=
    (cylinderReflectionCenterShift n).injective
  rw [projectivePolar_fibers, ← cylinderReflectionCenterShift_reflection,
    hinj.eq_iff, hinj.eq_iff]



theorem reflection_open_region_projective_comparison
    {Q : GeneralizedSliceCarrier.{u}}
    (q : RoundCylinderSpace → Q.carrier)
    (hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (n : ℤ) {C : Set RoundCylinderSpace} (hC : IsOpen C)
    (hfibers : ∀ x ∈ C, ∀ y ∈ C, q x = q y ↔ x = y ∨ x = cylinderIntegerReflection n y) :
    ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) Q.carrier projectiveCarrier.{u}.carrier ∞,
      e.source = q '' C ∧
      e.target = (projectivePolarMap L ∘ cylinderReflectionCenterShift n) '' C ∧
      ∀ x ∈ C, e (q x) = projectivePolarMap L (cylinderReflectionCenterShift n x) := by
  let : Nonempty RoundCylinderSpace := ⟨(⟨EuclideanSpace.single 0 1, by simp⟩, 0)⟩
  let f := projectivePolarMap.{u} L ∘ cylinderReflectionCenterShift n
  have hf : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f := fun x =>
    ((cylinderReflectionCenterShift n).isLocalDiffeomorph x).comp
      (𝓡 3) projectiveCarrier.carrier (projectivePolar_localDiffeomorph L _)
  exact exists_partialDiffeomorph_of_matching_local_covers ((𝓡 2).prod 𝓘(ℝ, ℝ)) q f hq hf hC
    (fun x hx y hy => (hfibers x hx y hy).trans (centeredProjectivePolar_fibers L n x y).symm)




theorem reflection_component_projective_comparison
    {Q : GeneralizedSliceCarrier.{u}}
    (q : RoundCylinderSpace → Q.carrier)
    (hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (n : ℤ) {U : Set Q.carrier} (hU : IsOpen U) (a : RoundCylinderSpace)
    {K : Set Q.carrier} (hK : IsPreconnected K) (hKU : K ⊆ U) (hKa : q a ∈ K)
    (hcompact : IsCompact (closure (connectedComponentIn (q ⁻¹' U) a)))
    (hfibers : ∀ x ∈ connectedComponentIn (q ⁻¹' U) a,
      ∀ y ∈ connectedComponentIn (q ⁻¹' U) a,
        q x = q y ↔ x = y ∨ x = cylinderIntegerReflection n y) :
    ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) Q.carrier projectiveCarrier.{u}.carrier ∞,
      e.source = q '' connectedComponentIn (q ⁻¹' U) a ∧ K ⊆ e.source ∧
      ∀ x ∈ connectedComponentIn (q ⁻¹' U) a,
        e (q x) = projectivePolarMap L (cylinderReflectionCenterShift n x) := by
  let : LocallyConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  have hC : IsOpen (connectedComponentIn (q ⁻¹' U) a) :=
    (hU.preimage hq.contMDiff.continuous).connectedComponentIn
  obtain ⟨e, hes, _, he⟩ := reflection_open_region_projective_comparison q hq L n hC hfibers
  refine ⟨e, hes, ?_, he⟩
  rw [hes]
  exact connected_subset_image_precompact_component q hq.contMDiff.continuous
    hq.isLocalHomeomorph.isOpenMap hU (hKU hKa) hcompact hK hKU hKa



theorem reflection_comparison_affine_collar
    {Q : GeneralizedSliceCarrier.{u}} (q : RoundCylinderSpace → Q.carrier)
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (n : ℤ)
    {C : Set RoundCylinderSpace}
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) Q.carrier projectiveCarrier.{u}.carrier ∞)
    (he : ∀ x ∈ C, e (q x) = projectivePolarMap L (cylinderReflectionCenterShift n x))
    (z : UnitTwoSphere) {t : ℝ} (ht : (n : ℝ) / 2 < t) (hz : (z, t) ∈ C) :
    e (q (z, t)) = projectiveAffineMap L ((t - (n : ℝ) / 2)⁻¹ • z.val) := by
  rw [he _ hz]
  exact projectivePolar_affine L z (sub_pos.mpr ht)

end PoincareConjecture.M38
