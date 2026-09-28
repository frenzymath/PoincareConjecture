import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGlobalPair
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}




theorem horizontalJacobiPair_unique_at (R : M14SquareRootPath G p)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {f g : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}
    (hf : IsHorizontalJacobiPairOn R (Real.sqrt a) (Real.sqrt b) f)
    (hg : IsHorizontalJacobiPairOn R (Real.sqrt a) (Real.sqrt b) g)
    {c : ℝ} (hc : c ∈ M14SqrtParameterInterval a b) (hinit : f c = g c) :
    ∀ s ∈ M14SqrtParameterInterval a b, f s = g s := by
  let C := M14SqrtParameterInterval a b
  let P := fun s t : ℝ => f s = g s → f t = g t
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  have hlocal : ∀ t ∈ C, ∀ᶠ s in 𝓝[C] t, P t s ∧ P s t := by
    intro t ht
    obtain ⟨j, N, β, hN, htN, hβ, hrec, hclock⟩ := exists_squareRoot_gauge_neighborhood R ht
    obtain ⟨l, r, hal, hlr, hrb, hlt, htr, hsubN, hnear⟩ :=
      M08.exists_enlarged_closed_interval hf.ordered ht.1 le_rfl ht.2 hN
        (fun s hs => (le_antisymm hs.2 hs.1) ▸ htN)
    have hsub : Icc l r ⊆ C ∩ N :=
      fun _ hs => ⟨Icc_subset_Icc hal hrb hs, hsubN hs⟩
    let W := Classical.choice (ordinaryGaugeWitness_nonempty j hCoordinates)
    have huniq {t₀ : ℝ} (ht₀ : t₀ ∈ Icc l r) (hfg : f t₀ = g t₀) :
        ∀ s ∈ Icc l r, f s = g s :=
      gaugeHorizontalJacobiPair_unique j hCoordinates hscalar W hM04 (β t).2
        (hβ.mono hsub) (fun s hs => hrec s (hsub hs)) (fun s hs => hclock s (hsub hs))
        (hf.restrict hal hlr hrb) (hg.restrict hal hlr hrb) ht₀ hfg
    filter_upwards [hnear t ⟨le_rfl, le_rfl⟩] with s hs
    exact ⟨fun h => huniq ⟨hlt, htr⟩ h s hs, fun h => huniq hs h t ⟨hlt, htr⟩⟩
  intro s hs
  have hprop := isPreconnected_Icc.induction₂' P hlocal
    (fun _ _ _ _ _ _ hst htu => htu ∘ hst) hc hs
  exact hprop hinit

end PoincareConjecture.M14
