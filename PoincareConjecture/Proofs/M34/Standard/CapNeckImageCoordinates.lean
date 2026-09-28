import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets
import PoincareConjecture.Proofs.M34.Mathlib.PartialImageTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem capShiftedCoordinate_mem {epsilon c : ℝ}
    (hdom : Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    N.coordinate_map (z.1, z.2 + c) ∈ N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) := by
  have hs : z.2 + c ∈ Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  refine ⟨N.coordinate_map_mem_of_axial_mem (hdom hs), ?_⟩
  rw [N.coordinate_inverse_coordinate_map_of_axial_mem (hdom hs)]
  exact hs



theorem capShiftedCoordinate_contMDiffOn {epsilon c : ℝ}
    (hdom : Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun z : RoundCylinderSpace => N.coordinate_map (z.1, z.2 + c))
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
  apply N.coordinate_map_smooth.comp
    (contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)).contMDiffOn
  intro z hz
  change (z.1, z.2 + c) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  exact ⟨mem_univ _, hdom ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩



noncomputable def capShiftedCoordinate {epsilon c : ℝ}
    (hdom : Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    NeckDomain epsilon ≃ₜ N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) := by
  have hinv (x : N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c)) :
      (N.coordinate_inverse x).2 - c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    constructor <;> linarith [x.property.2.1, x.property.2.2]
  have hmap : Continuous (fun z : NeckDomain epsilon =>
      N.coordinate_map (z.1, (z.2 : ℝ) + c)) :=
    (N.coordinate_map_smooth.continuousOn).comp_continuous
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).add continuous_const))
      (fun z => ⟨mem_univ _, hdom
        ⟨by linarith [z.2.property.1], by linarith [z.2.property.2]⟩⟩)
  have hinvcont : Continuous (fun x : N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) =>
      N.coordinate_inverse (x : M)) :=
    N.coordinate_inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property.1)
  refine {
    toFun := fun z => ⟨N.coordinate_map (z.1, (z.2 : ℝ) + c),
      N.capShiftedCoordinate_mem hdom (z := (z.1, (z.2 : ℝ))) z.2.property⟩
    invFun := fun x => ((N.coordinate_inverse x).1,
      ⟨(N.coordinate_inverse x).2 - c, hinv x⟩)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := hmap.subtype_mk _
    continuous_invFun := hinvcont.fst.prodMk ((hinvcont.snd.sub continuous_const).subtype_mk _)
  }
  · intro z
    have hz := N.coordinate_inverse_coordinate_map_of_axial_mem
      (z := (z.1, (z.2 : ℝ) + c))
      (hdom ⟨by linarith [z.2.property.1], by linarith [z.2.property.2]⟩)
    apply _root_.Prod.ext
    · exact congrArg (fun y : RoundCylinderSpace => y.1) hz
    · apply Subtype.ext
      exact (congrArg (fun y : RoundCylinderSpace => y.2 - c) hz).trans (add_sub_cancel_right _ _)
  · intro x
    apply Subtype.ext
    dsimp only
    rw [sub_add_cancel]
    exact N.coordinate_map_coordinate_inverse x.property.1

variable {X : Type v} [TopologicalSpace X]



noncomputable def capImageRegionHomeomorph (e : OpenPartialHomeomorph M X)
    {epsilon c : ℝ}
    (hsource : N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆ e.source) :
    N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ≃ₜ
      e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) := by
  have hinv (y : e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c)) :
      e.symm y ∈ N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) := by
    obtain ⟨x, hx, heq⟩ := y.property
    rw [← heq, e.left_inv (hsource hx)]
    exact hx
  have htarget : e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hsource hx)
  refine {
    toFun := fun x => ⟨e x, mem_image_of_mem e x.property⟩
    invFun := fun y => ⟨e.symm y, hinv y⟩
    left_inv := fun x => Subtype.ext (e.left_inv (hsource x.property))
    right_inv := fun y => Subtype.ext (e.right_inv (htarget y.property))
    continuous_toFun := (e.continuousOn.comp_continuous continuous_subtype_val
      (fun x => hsource x.property)).subtype_mk _
    continuous_invFun := (e.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun y => htarget y.property)).subtype_mk _
  }

end PoincareConjecture.EpsilonNeck
