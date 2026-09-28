import PoincareConjecture.Proofs.M14.Sec6_3_FamilyDensity
import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyPrimitive

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def squareFamilyAction (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ × P → G.Point) (C : Set ℝ) (a b : ℝ) (p : P) : ℝ :=
  ∫ s in a..b, squareCurveDensity G (fun r => γ (r, p)) C s

set_option maxHeartbeats 800000 in

theorem squareFamilyAction_contDiffOn [FiniteDimensional ℝ P]
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {a b c : ℝ} (hab : a < b)
    {U : Set P} (hU : IsOpen U) {γ : ℝ × P → G.Point}
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ γ (Icc a b ×ˢ U))
    (hc : c ∈ Icc a b) :
    ContDiffOn ℝ ∞ (squareFamilyAction G γ (Icc a b) a c) U := by
  let f : ℝ × P → ℝ := fun z => squareCurveDensity G (fun r => γ (r, z.2)) (Icc a b) z.1
  have hd : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U) :=
    squareFamilyDensity_contDiffOn hM12 (uniqueDiffOn_Icc hab) hU hγ
  have hi : ContDiffOn ℝ ∞ (fun z : P × ℝ => ∫ s in a..z.2, f (s, z.1)) (U ×ˢ Icc a b) :=
    closedFamilyPrimitive_contDiffOn (E := P) (F := ℝ) hab hU f hd
  change ContDiffOn ℝ ∞ (fun p : P => ∫ s in a..c, f (s, p)) U
  exact hi.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hc⟩)

end PoincareConjecture.M14
