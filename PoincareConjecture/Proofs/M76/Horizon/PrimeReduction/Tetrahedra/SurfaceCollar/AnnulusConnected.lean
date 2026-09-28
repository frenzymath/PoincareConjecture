import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSides

set_option autoImplicit false
open Set Geometry PLAnnularStrip
namespace PoincareConjecture.M76

theorem isPreconnected_complete_squareAnnulus {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) : IsPreconnected (squareAnnulus L d) := by
  have himage : wrappedStripMap L '' rectangle (4 * L) d = squareAnnulus L d := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      have ht : 4 * |q.2| < L := lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (abs_le.mpr hq.2) (by norm_num)) hwidth
      apply mem_squareAnnulus_iff_depth.mpr
      rw [←annulusMap_coe (by linarith) ht hq.1,depth_annulusMap (by linarith) ht]
      exact hq.2
    · intro hp
      obtain ⟨s,hs,hsp⟩ := exists_period_parameter_of_depth hd hwidth ⟨p,hp⟩
      have hu := mem_squareAnnulus_iff_depth.mp hp
      refine ⟨(s,depth L p),⟨hs,hu⟩,?_⟩
      rw [←annulusMap_coe (by linarith)
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hu) (by norm_num)) hwidth) hs]
      exact hsp.symm
  rw [←himage]
  exact ((convex_Icc _ _).prod (convex_Icc _ _)).isPreconnected.image _
    (finitePiecewiseAffineOn_wrappedStripMap hd hwidth).continuousOn

end PoincareConjecture.M76
