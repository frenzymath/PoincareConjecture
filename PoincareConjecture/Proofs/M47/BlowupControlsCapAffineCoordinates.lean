import PoincareConjecture.Proofs.M47.CanonicalNeckCompressedCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem affine_inverse_mem {lambda c e s : ℝ} (hlambda : 0 < lambda) :
    (s - c) / lambda ∈ Ioo (-e) e ↔ s ∈ Ioo (c - lambda * e) (c + lambda * e) := by
  rw [mem_Ioo, mem_Ioo, lt_div_iff₀ hlambda, div_lt_iff₀ hlambda]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith [h.1, h.2]

noncomputable def capAffineNeckCoordinate (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hlambda : 0 < lambda)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    NeckDomain epsilon ≃ₜ N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹) := by
  let inc : NeckDomain epsilon → NeckDomain N.epsilon := fun z =>
    (z.1, ⟨lambda * z.2 + c, hdomain z.2 z.2.property⟩)
  have hinc : Continuous inc := continuous_fst.prodMk
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).add
      continuous_const |>.subtype_mk _)
  have hleft (z : NeckDomain epsilon) :
      neckAxialInverse lambda c (N.coordinate_inverse (N.coordinate (inc z))) =
        (z.1, (z.2 : ℝ)) := by
    rw [N.coordinate_inverse_left]
    exact neckAxialInverse_left hlambda.ne' c (z.1, z.2)
  have hmap (z : NeckDomain epsilon) :
      (N.coordinate (inc z) : M) ∈
        N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹) := by
    refine ⟨(N.coordinate (inc z)).property, ?_⟩
    rw [N.coordinate_inverse_left]
    change lambda * (z.2 : ℝ) + c ∈ Ioo _ _
    apply (affine_inverse_mem hlambda).mp
    simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _ hlambda.ne'] using z.2.property
  have hinvmem (x : N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹)) :
      (neckAxialInverse lambda c (N.coordinate_inverse x)).2 ∈
        Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    (affine_inverse_mem hlambda).mpr x.property.2
  have hinvcont : Continuous
      (fun x : N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹) =>
        neckAxialInverse lambda c (N.coordinate_inverse (x : M))) :=
    (neckAxialInverse_contMDiff lambda c).continuous.comp
      (N.coordinate_inverse_smooth.continuousOn.comp_continuous
        continuous_subtype_val (fun x => x.property.1))
  refine {
    toFun := fun z => ⟨N.coordinate (inc z), hmap z⟩
    invFun := fun x => ((neckAxialInverse lambda c (N.coordinate_inverse x)).1,
      ⟨(neckAxialInverse lambda c (N.coordinate_inverse x)).2, hinvmem x⟩)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun :=
      (continuous_subtype_val.comp (N.coordinate.continuous.comp hinc)).subtype_mk _
    continuous_invFun := hinvcont.fst.prodMk (hinvcont.snd.subtype_mk _)
  }
  · intro z
    apply Prod.ext
    · exact congrArg (fun y : RoundCylinderSpace => y.1) (hleft z)
    · exact Subtype.ext (congrArg (fun y : RoundCylinderSpace => y.2) (hleft z))
  · intro x
    apply Subtype.ext
    rw [N.coordinate_map_eq]
    change N.coordinate_map (neckAxialSpaceMap lambda c
      (neckAxialInverse lambda c (N.coordinate_inverse x))) = x
    rw [neckAxialInverse_right hlambda.ne']
    have h := congrArg (fun y : N.carrier => (y : M))
      (N.coordinate_inverse_right x x.property.1)
    rw [N.coordinate_map_eq] at h
    exact h

theorem capAffineNeckCoordinate_map_eq (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hlambda : 0 < lambda)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (z : NeckDomain epsilon) :
    (capAffineNeckCoordinate N hlambda hdomain z : M) =
      N.coordinate_map (neckAxialSpaceMap lambda c (z.1, (z.2 : ℝ))) :=
  N.coordinate_map_eq _

theorem capAffineNeckCoordinate_inverse_left (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hlambda : 0 < lambda)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (z : NeckDomain epsilon) :
    neckAxialInverse lambda c
        (N.coordinate_inverse (capAffineNeckCoordinate N hlambda hdomain z)) =
      (z.1, (z.2 : ℝ)) := by
  rw [capAffineNeckCoordinate_map_eq,
    N.coordinate_inverse_coordinate_map_of_axial_mem (hdomain z.2 z.2.property)]
  exact neckAxialInverse_left hlambda.ne' c _

theorem capAffineNeckCoordinate_inverse_mem (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hlambda : 0 < lambda) {x : M}
    (hx : x ∈ N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹)) :
    neckAxialInverse lambda c (N.coordinate_inverse x) ∈
      univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
  ⟨mem_univ _, (affine_inverse_mem hlambda).mpr hx.2⟩

theorem capAffineNeckCoordinate_map_smooth (N : EpsilonNeck g)
    {epsilon lambda c : ℝ}
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (N.coordinate_map ∘ neckAxialSpaceMap lambda c)
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
  apply N.coordinate_map_smooth.comp (neckAxialSpaceMap_contMDiff lambda c).contMDiffOn
  exact fun z hz => ⟨mem_univ _, hdomain z.2 hz.2⟩

theorem capAffineNeckCoordinate_inverse_smooth (N : EpsilonNeck g)
    (epsilon lambda c : ℝ) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (neckAxialInverse lambda c ∘ N.coordinate_inverse)
      (N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹)) :=
  (neckAxialInverse_contMDiff lambda c).comp_contMDiffOn
    (N.coordinate_inverse_smooth.mono (fun _ hx => hx.1))

end PoincareConjecture.M47
