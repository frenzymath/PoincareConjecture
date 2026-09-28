import PoincareConjecture.Definitions.M45SmallNecks
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Scale










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M45



theorem smallNeckThreshold :
    ∃ epsilon₁ : ℝ, 0 < epsilon₁ ∧ M45SmallNeckScaleBound.{u} epsilon₁ := by
  obtain ⟨epsilon₁, hpos, _, hbound⟩ :=
    RiemannianMetric.exists_universal_neck_scale_lower_bound.{u}
  refine ⟨epsilon₁, hpos, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ g D hcomplete hpositive epsilon hepsilon hsmall
  cases isEmpty_or_nonempty M with
  | inl hempty =>
    exact ⟨1, zero_lt_one, fun N _ _ => isEmptyElim N.center⟩
  | inr hnonempty =>
    obtain ⟨scale₀, hscale₀, hscale⟩ := hbound M g D hcomplete
      (fun x v w hv hw hvw => hpositive x v w ⟨hv, hw, hvw⟩)
      epsilon hepsilon hsmall
    exact ⟨scale₀, hscale₀, fun N _ hN => hscale N hN⟩

end PoincareConjecture.M45
