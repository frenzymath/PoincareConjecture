import PoincareConjecture.Proofs.M38.Components

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

attribute [local instance] SphereBundleCircleModel.carrier_topology
  SphereBundleCircleModel.carrier_charted SphereBundleCircleModel.carrier_manifold

noncomputable def bundleAlongDiffeomorph (Q : SphereBundleCircleModel.{u})
    {S : GeneralizedSliceCarrier.{u}}
    (d : Diffeomorph (𝓡 3) (𝓡 3) S.carrier Q.carrier ∞) : SurgerySphereBundle S where
  projection := Q.projection ∘ d
  projection_continuous := Q.projection_continuous.comp d.continuous
  projection_surjective := Q.projection_surjective.comp d.surjective
  projection_smooth := Q.projection_smooth.comp d.contMDiff
  local_trivialization := by
    intro b
    obtain ⟨U, hU, hb, f, g, himage, hleft, hright, hf, hg, hp⟩ :=
      Q.local_trivialization b
    refine ⟨U, hU, hb, f ∘ d, d.symm ∘ g, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (f ∘ d) '' (d ⁻¹' (Q.projection ⁻¹' U)) = _
      rw [Set.image_comp]
      have hd : d '' (d ⁻¹' (Q.projection ⁻¹' U)) = Q.projection ⁻¹' U :=
        Set.image_preimage_eq _ d.surjective
      exact (congrArg (fun V => f '' V) hd).trans himage
    · intro x hx
      change d.symm (g (f (d x))) = x
      rw [hleft hx, d.symm_apply_apply]
    · intro x hx
      change f (d (d.symm (g x))) = x
      rw [d.apply_symm_apply, hright hx]
    · exact hf.comp d.contMDiff.contMDiffOn (fun _ hx => hx)
    · exact d.symm.contMDiff.comp_contMDiffOn hg
    · intro x hx
      exact hp (d x) hx

noncomputable def componentBundleDiffeomorph (S : GeneralizedSliceCarrier.{u})
    {g : RiemannianMetric 3 S.carrier} {X : Set S.carrier}
    (Q : SphereBundleCircleCertificate g X) (x : S.carrier)
    (hcarrier : Q.carrier = connectedComponent x) :
    Diffeomorph (𝓡 3) (𝓡 3) (componentCarrier S x).carrier Q.model.carrier ∞ := by
  let inverse : Q.model.carrier → (componentCarrier S x).carrier := fun y =>
    ⟨Q.inverse y, hcarrier.subset (by
      rw [Q.inverse_eq y]
      exact (Q.homeomorph.symm y).property)⟩
  refine {
    toEquiv := {
      toFun := fun y => Q.forward y.1
      invFun := inverse
      left_inv := ?_
      right_inv := ?_ }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro y
    apply Subtype.ext
    change Q.inverse (Q.forward y.1) = y.1
    have hy : y.1 ∈ Q.carrier := hcarrier.symm.subset y.property
    calc
      Q.inverse (Q.forward y.1) = Q.inverse (Q.homeomorph ⟨y.1, hy⟩) :=
        congrArg Q.inverse (Q.forward_eq ⟨y.1, hy⟩)
      _ = (Q.homeomorph.symm (Q.homeomorph ⟨y.1, hy⟩)).1 := Q.inverse_eq _
      _ = y.1 := congrArg Subtype.val (Q.homeomorph.symm_apply_apply ⟨y.1, hy⟩)
  · intro y
    change Q.forward (Q.inverse y) = y
    exact (congrArg Q.forward (Q.inverse_eq y)).trans
      ((Q.forward_eq (Q.homeomorph.symm y)).trans (Q.homeomorph.apply_symm_apply y))
  · apply contMDiffOn_univ.mp
    exact Q.forward_smooth.comp
      (contMDiff_subtype_val (U := componentOpen S x)).contMDiffOn
      (fun y _ => hcarrier.symm.subset y.property)
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen S x) inverse).mp
    exact Q.inverse_smooth

noncomputable def bundleOnComponent (S : GeneralizedSliceCarrier.{u})
    {g : RiemannianMetric 3 S.carrier} {X : Set S.carrier}
    (Q : SphereBundleCircleCertificate g X) (x : S.carrier)
    (hcarrier : Q.carrier = connectedComponent x) :
    SurgerySphereBundle (componentCarrier S x) :=
  bundleAlongDiffeomorph Q.model (componentBundleDiffeomorph S Q x hcarrier)

end PoincareConjecture.M38
