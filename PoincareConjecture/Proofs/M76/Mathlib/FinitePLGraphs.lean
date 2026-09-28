import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem FinitePiecewiseAffineOn.graph {f : E → F} {s : Set E}
    (hf : FinitePiecewiseAffineOn f s) :
    FinitePiecewiseAffineOn (fun x => (x, f x)) s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  refine ⟨K, hK, rfl, fun r hr => ?_⟩
  obtain ⟨a, ha⟩ := hfaces r hr
  exact ⟨(ContinuousAffineMap.id ℝ E).prod a, fun x hx => Prod.ext rfl (ha hx)⟩

end Geometry

namespace Set




theorem IsFinitePLBallPair.graph {V E F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s b : Set E} (hs : IsFinitePLBallPair V s b)
    {f : E → F} (hf : FinitePiecewiseAffineOn f s) :
    IsFinitePLBallPair V ((fun x => (x, f x)) '' s) ((fun x => (x, f x)) '' b) :=
  hs.image hf.graph (fun _ _ _ _ h => congrArg Prod.fst h)

end Set
