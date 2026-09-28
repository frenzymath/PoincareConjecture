import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetNorm
import PoincareConjecture.Definitions.Ch12.StandardCap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

noncomputable def StandardCylinderPatch.restrict {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) {l : ℝ} (hl : 0 < l) (hlL : l ≤ length) :
    StandardCylinderPatch l x := by
  let V : Set StandardCylinderSpace := univ ×ˢ Ioo (-l) l
  have hsub : V ⊆ univ ×ˢ Ioo (-length) length :=
    prod_mono subset_rfl (Ioo_subset_Ioo (neg_le_neg hlL) hlL)
  refine {
    length_pos := hl
    carrier := N.carrier ∩ N.inverse ⁻¹' V
    carrier_open := N.inverse_smooth.continuousOn.isOpen_inter_preimage
      N.carrier_open (isOpen_univ.prod isOpen_Ioo)
    coordinate := N.coordinate
    inverse := N.inverse
    coordinate_image := ?_
    coordinate_left_inverse := N.coordinate_left_inverse.mono hsub
    coordinate_right_inverse := N.coordinate_right_inverse.mono inter_subset_left
    inverse_domain := fun _ hy => hy.2.2
    coordinate_smooth := N.coordinate_smooth.mono hsub
    inverse_smooth := N.inverse_smooth.mono inter_subset_left
    center_sphere := N.center_sphere
  }
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨N.coordinate_image ▸ mem_image_of_mem N.coordinate (hsub hz), ?_⟩
    change N.inverse (N.coordinate z) ∈ V
    rwa [N.coordinate_left_inverse (hsub hz)]
  · intro y hy
    exact ⟨N.inverse y, hy.2, N.coordinate_right_inverse hy.1⟩

namespace M35

theorem roundCylinderJetErrorSquared_mono_order {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) {r s : ℕ} (hrs : r ≤ s) :
    roundCylinderJetErrorSquared u B r z ≤ roundCylinderJetErrorSquared u B s z := by
  unfold roundCylinderJetErrorSquared
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hrs 1))
    (fun k _ _ => roundCylinderTensorNormSquared_nonneg hu z.1 z.2 _)

end M35

theorem RoundCylinderFamilyClose.restrict_bound {delta epsilon : ℝ} {I : Set ℝ}
    {B : ℝ → RoundCylinderTwoTensor} (h : RoundCylinderFamilyClose delta I B)
    (hd : 0 < delta) (hde : delta ≤ epsilon) (hI : ∀ u ∈ I, u < 1) :
    (∀ u ∈ I, RoundCylinderTensorSmoothOn epsilon (B u)) ∧
      ∃ bound : ℝ, bound < delta ^ 2 ∧
        ∀ u ∈ I, ∀ z : RoundCylinderSpace,
          z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
            roundCylinderJetErrorSquared u (B u) ⌊epsilon⁻¹⌋₊ z ≤ bound := by
  have hinv : epsilon⁻¹ ≤ delta⁻¹ := inv_anti₀ hd hde
  have hsub := Ioo_subset_Ioo (neg_le_neg hinv) hinv
  refine ⟨fun u hu q a b => (h.1 u hu q a b).mono (prod_mono subset_rfl hsub), ?_⟩
  obtain ⟨bound, hb, hjet⟩ := h.2
  exact ⟨bound, hb, fun u hu z hz =>
    (M35.roundCylinderJetErrorSquared_mono_order (hI u hu) (B u) z
      (Nat.floor_mono hinv)).trans (hjet u hu z (hsub hz))⟩

theorem StandardSpacetimeCylinderClose.restrict (A : StandardCylinderAtlas)
    (g : ℝ → RiemannianMetric 3 StandardCapSpace)
    {delta epsilon origin scale : ℝ} {I : Set ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch delta⁻¹ x)
    (h : StandardSpacetimeCylinderClose A g delta origin scale I N)
    (hd : 0 < delta) (hde : delta ≤ epsilon) (hI : ∀ u ∈ I, u < 1) :
    StandardSpacetimeCylinderClose A g epsilon origin scale I
      (N.restrict (inv_pos.mpr (hd.trans_le hde)) (inv_anti₀ hd hde)) := by
  obtain ⟨hs, bound, hb, hjet⟩ := h.restrict_bound hd hde hI
  exact ⟨hs, bound, hb.trans_le (pow_le_pow_left₀ hd.le hde 2), hjet⟩

end PoincareConjecture
