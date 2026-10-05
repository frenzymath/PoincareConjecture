import PoincareLib.Geometry.RicciFlow.Surgery.Control.SmallNecks
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Scale

/-!
# Proposition 2.19 for the Chapter 15 threshold

Morgan--Tian, Proposition 2.19 and Lemma 2.20, pp. 31-33. The lower M20
proof already establishes the uniform threshold using soul separation and
Busemann flux. This adapter retains M45's orthonormal-pair formulation and
its connection-equality filter without strengthening any hypothesis.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M45

/-- Proposition 2.19, pp. 31-33, supplies the first threshold in
the minimum of Section 15.1.1, p. 354. -/
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

end PoincareMT.M45
