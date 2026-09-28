import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPositivePart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.CommonSimplicialRefinement

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

variable [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.prod_mk {f : E → F} {g : E → G} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => (f x, g x)) S := by
  obtain ⟨K, hK, hKS, hfK⟩ := hf
  obtain ⟨L, hL, hLS, hgL⟩ := hg
  obtain ⟨R, hR, hRK, hRL⟩ :=
    SimplicialComplex.exists_common_finite_subdivision K L hK hL (hKS.trans hLS.symm)
  refine ⟨R, hR, hRK.space_eq.trans hKS, fun s hs => ?_⟩
  obtain ⟨a, ha⟩ := hRK.affineOnFaces hfK s hs
  obtain ⟨b, hb⟩ := hRL.affineOnFaces hgL s hs
  exact ⟨a.prod b, fun x hx => Prod.ext (ha hx) (hb hx)⟩

theorem FinitePiecewiseAffineOn.add {f g : E → F} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => f x + g x) S :=
  (hf.prod_mk hg).postcomp
    (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F).toContinuousAffineMap

theorem FinitePiecewiseAffineOn.sub {f g : E → F} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => f x - g x) S :=
  (hf.prod_mk hg).postcomp
    (ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F).toContinuousAffineMap

end Geometry
