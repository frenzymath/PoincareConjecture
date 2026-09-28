import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryGeometry












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

set_option backward.isDefEq.respectTransparency false in


noncomputable def ordinaryChapter11Cylinder
    (p : (ordinaryChapter11Flow R).point) (scale : ℝ) (hscale : 0 < scale)
    (K : Set ℝ) (U : Set ((ordinaryChapter11Flow R).slice p.1).carrier)
    (hK : ∀ s ∈ K, p.1 + s / scale ∈ I.domain) :
    GeneralizedFlowCylinder (ordinaryChapter11Flow R)
      ((ordinaryChapter11Flow R).slice p.1) p.1 scale K U := by
  let t0 : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  let phi0 := R.product.sliceIdentification t0
  let phi (s : ℝ) (hs : s ∈ K) := R.product.sliceIdentification ⟨p.1 + s / scale, hK s hs⟩
  refine {
    scale_pos := hscale
    forward := fun s hs => phi s hs ∘ phi0.symm
    inverse := fun s hs => phi0 ∘ (phi s hs).symm
    forward_smooth := fun s hs => ((phi s hs).contMDiff.comp phi0.symm.contMDiff).contMDiffOn
    inverse_smooth := fun s hs => (phi0.contMDiff.comp (phi s hs).symm.contMDiff).contMDiffOn
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := ?_
  }
  · intro s hs x _
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply]
  · intro s hs x _
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply]
  · let := ordinaryChapter11Topology R.product
    let clock := (Homeomorph.mulRight₀ scale (ne_of_gt hscale)).symm.trans
      (Homeomorph.addLeft p.1)
    have hc : Topology.IsEmbedding (fun s : K => p.1 + s.val / scale) := by
      simpa only [clock, Homeomorph.trans_apply, Homeomorph.mulRight₀_symm_apply,
        Homeomorph.coe_addLeft, Function.comp_def, div_eq_mul_inv] using
        clock.isEmbedding.comp (Topology.IsEmbedding.subtypeVal (p := (· ∈ K)))
    let f : K → I.domain := fun s => ⟨p.1 + s.val / scale, hK s.val s.property⟩
    have hf : Topology.IsEmbedding f := hc.codRestrict I.domain (fun s => hK s.val s.property)
    have hx : Topology.IsEmbedding (fun x : U => phi0.symm x.val) :=
      phi0.symm.toHomeomorph.isEmbedding.comp .subtypeVal
    have he := (ordinaryChapter11Homeomorph R.product).symm.isEmbedding.comp (hf.prodMap hx)
    have hmap : (fun z : K × U =>
        (⟨p.1 + z.1.val / scale, phi z.1.val z.1.property (phi0.symm z.2.val)⟩ :
          (ordinaryChapter11Flow R).point)) =
        (ordinaryChapter11Homeomorph R.product).symm ∘
          Prod.map f (fun x : U => phi0.symm x.val) := by
      funext z
      apply (ordinaryChapter11Flatten R.product).injective
      exact R.product.sliceIdentification_eq _ _
    change Topology.IsEmbedding (fun z : K × U =>
      (⟨p.1 + z.1.val / scale, phi z.1.val z.1.property (phi0.symm z.2.val)⟩ :
        (ordinaryChapter11Flow R).point))
    rw [hmap]
    exact he
  · intro s hs x _
    refine ⟨⟨()⟩, phi0.symm x, 1, zero_lt_one, ?_⟩
    intro s' hs' _
    exact ⟨hK s' hs', rfl⟩



theorem ordinaryChapter11Cylinder_zero_identity
    (p : (ordinaryChapter11Flow R).point) (scale : ℝ) (hscale : 0 < scale)
    (K : Set ℝ) (U : Set ((ordinaryChapter11Flow R).slice p.1).carrier)
    (hK : ∀ s ∈ K, p.1 + s / scale ∈ I.domain) (hzero : 0 ∈ K)
    (x : ((ordinaryChapter11Flow R).slice p.1).carrier) :
    (ordinaryChapter11Cylinder R p scale hscale K U hK).pointMap 0 hzero x = ⟨p.1, x⟩ := by
  apply ordinaryChapter11Point_ext R
  · change p.1 + 0 / scale = p.1
    simp only [zero_div, add_zero]
  · change (R.product.sliceIdentification ⟨p.1 + 0 / scale, hK 0 hzero⟩
      ((R.product.sliceIdentification
        ⟨p.1, ordinaryChapter11Point_time_mem R p⟩).symm x)).val.2 = x.val.2
    rw [R.product.sliceIdentification_eq]
    exact ordinaryChapter11_inverse_projection R
      ⟨p.1, ordinaryChapter11Point_time_mem R p⟩ x

end PoincareConjecture.M34
