import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Expansion

/-! # Restricting a cylinder comparison to a weaker requested accuracy -/

set_option autoImplicit false

open Set

namespace PoincareMT.NoncompactKappa.Positive

theorem roundCylinderClose_mono {epsilon delta u : ℝ} {B : RoundCylinderTwoTensor}
    (he : 0 < epsilon) (hed : epsilon ≤ delta) (hu : u < 1)
    (hB : RoundCylinderClose epsilon u B) : RoundCylinderClose delta u B := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨?_, bound, hbound.trans_le (pow_le_pow_left₀ he.le hed 2), ?_⟩
  · intro q a b
    exact (hsmooth q a b).mono
      (Set.prod_mono subset_rfl (DeepHorn.neckInterval_subset he hed))
  · intro z hz
    exact (DeepHorn.evolvingCylinderJetErrorSquared_mono hu B z
      (Nat.floor_mono ((inv_le_inv₀ (he.trans_le hed) he).2 hed))).trans
      (hjet z (DeepHorn.neckInterval_subset he hed hz))

end PoincareMT.NoncompactKappa.Positive
