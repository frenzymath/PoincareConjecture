import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapse

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePiecewiseAffineOn_clip {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => clip r (t x)) S := by
  have hconst (a : ℝ) : FinitePiecewiseAffineOn (fun _ : E => a) S :=
    (ht.postcomp (ContinuousAffineMap.const ℝ ℝ a)).congr (fun _ _ => rfl)
  exact (hconst (-r)).max (ht.min (hconst r))

theorem finitePiecewiseAffineOn_height {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => height r (t x)) S := by
  have hc := finitePiecewiseAffineOn_clip ht r
  have hc2 := finitePiecewiseAffineOn_clip ht (2 * r)
  have htwice : FinitePiecewiseAffineOn (fun x => 2 * clip r (t x)) S :=
    (hc.postcomp ((2 : ℝ) • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  exact (ht.sub htwice).add hc2

theorem finitePiecewiseAffineOn_displacement {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => displacement r (t x)) S :=
  ht.sub (finitePiecewiseAffineOn_height ht r)

end CollarCollapse
