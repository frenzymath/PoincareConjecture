import PoincareConjecture.Proofs.M14.Sec6_2_SquareVariationConstruction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem exists_variationOfSquare_eqOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (R : M14SquareRootPath G p) (H : ℝ × ℝ → G.Point) {r : ℝ} (hr : 0 < r)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval a b ×ˢ Ioo (-r) r))
    (hclock : ∀ s ∈ M14SqrtParameterInterval a b, ∀ v ∈ Ioo (-r) r,
      G.spacetime.timeFunction (H (s, v)) = T - s ^ 2)
    (hzero : ∀ s ∈ M14SqrtParameterInterval a b, H (s, 0) = R.curve s) :
    ∃ V : M14LVariationData G p R, V.parameterDomain = Ioo (-r) r ∧
      ∀ s ∈ M14SqrtParameterInterval a b, ∀ v, V.squareFamily s v = H (s, v) := by
  classical
  let K : ℝ × ℝ → G.Point := fun z =>
    if z.1 ∈ M14SqrtParameterInterval a b then H z else R.curve z.1
  have heq (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b) (v : ℝ) : K (s, v) = H (s, v) :=
    if_pos hs
  have hK : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ K
      (M14SqrtParameterInterval a b ×ˢ Ioo (-r) r) :=
    hH.congr (fun z hz => heq z.1 hz.1 z.2)
  have htime (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b) (v : ℝ)
      (hv : v ∈ Ioo (-r) r) : G.spacetime.timeFunction (K (s, v)) = T - s ^ 2 := by
    rw [heq s hs v, hclock s hs v hv]
  have hcenter (s : ℝ) : K (s, 0) = R.curve s := by
    by_cases hs : s ∈ M14SqrtParameterInterval a b
    · exact (heq s hs 0).trans (hzero s hs)
    · exact if_neg hs
  exact ⟨variationOfSquare hM12 R K r hr hK htime hcenter, rfl, heq⟩

end PoincareConjecture.M14
