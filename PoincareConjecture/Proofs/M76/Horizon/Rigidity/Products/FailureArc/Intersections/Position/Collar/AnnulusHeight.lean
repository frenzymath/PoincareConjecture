import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.AnnulusHeightGraphs
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

noncomputable def planarAnnulusRimHeight (x : ℝ × ℝ) : ℝ :=
  min (1 - depth 8 x) (1 + depth 8 x)

theorem continuous_planarAnnulusRimHeight : Continuous planarAnnulusRimHeight :=
  (continuous_const.sub (continuous_depth 8)).min
    (continuous_const.add (continuous_depth 8))

theorem finitePiecewiseAffineOn_planarAnnulusRimHeight
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn planarAnnulusRimHeight K.space := by
  have hd := Dehn.finitePiecewiseAffineOn_annulus_depth K hK 8
  have hconst := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ (ℝ × ℝ) (1 : ℝ))).finitePiecewiseAffineOn hK
  exact (hconst.sub hd).min (hconst.add hd)

theorem planarAnnulusRimHeight_nonneg {x : ℝ × ℝ} (hx : x ∈ squareAnnulus 8 1) :
    0 ≤ planarAnnulusRimHeight x := by
  have hb := mem_squareAnnulus_iff_depth.mp hx
  exact le_min (by linarith [hb.2]) (by linarith [hb.1])

theorem planarAnnulusRimHeight_eq_zero_iff {x : ℝ × ℝ} (hx : x ∈ squareAnnulus 8 1) :
    planarAnnulusRimHeight x = 0 ↔ x ∈ frontier (squareAnnulus 8 1) := by
  rw [mem_frontier_squareAnnulus_iff (by norm_num) (by norm_num) hx]
  by_cases hd : 0 ≤ depth 8 x
  · rw [planarAnnulusRimHeight, min_eq_left (by linarith), abs_of_nonneg hd]
    constructor <;> intro h <;> linarith
  · rw [planarAnnulusRimHeight, min_eq_right (by linarith), abs_of_neg (lt_of_not_ge hd)]
    constructor <;> intro h <;> linarith

end PoincareConjecture.M76
