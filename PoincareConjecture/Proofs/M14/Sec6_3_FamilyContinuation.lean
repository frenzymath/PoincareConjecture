import PoincareConjecture.Proofs.M14.Sec6_3_PhaseContinuation
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeFamilyLift
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalCoherence
import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyGluing











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 800000 in





theorem initialValueCurve_smooth_tube_of_restart
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {T l r d : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hrd : r < d)
    {x : G.Point} (ζ : E → G.Horizontal x) {U : Set E} (hU : IsOpen U)
    {z₀ : E} (hz₀ : z₀ ∈ U)
    (hγ : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z => initialValueCurve G T x (ζ z.1) z.2) (U ×ˢ Icc 0 r))
    (hsurv : ∀ z ∈ U, (ζ z, r) ∈ initialValueDomain G T x)
    (β₀ : E × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (hβ₀ : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β₀
      (U ×ˢ Icc l r))
    (hrec₀ : ∀ z ∈ U ×ˢ Icc l r,
      (G.gaugeCover.cylinder b).toSpacetime (β₀ z) = initialValueCurve G T x (ζ z.1) z.2)
    (htime : ∀ s ∈ Icc l d, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (Φ : E → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hi : ∀ z ∈ U, Φ z = ((β₀ (z, r)).2.val,
      M08.chartMomentumVector (M08.chartActionMetric W.flow T x₀ (r, (β₀ (z, r)).2.val))
        (derivWithin (fun s => (β₀ (z, s)).2.val) (Icc l r) r)))
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hA : IsOpen A) (hcenter : Φ z₀ ∈ A)
    (Ψ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hΨ : ContDiffOn ℝ ∞ Ψ (A ×ˢ Icc l d))
    (hdata : ∀ y ∈ A, Ψ (y, r) = y ∧ ∀ s ∈ Icc l d,
      (Ψ (y, s)).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
        HasDerivWithinAt (fun t => Ψ (y, t))
          (M08.closedChartEulerPhase W.flow T x₀ (Icc l d) s (Ψ (y, s))) (Icc l d) s) :
    ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      (∀ z ∈ V ×ˢ Icc 0 d, (ζ z.1, z.2) ∈ initialValueDomain G T x) ∧
      ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
        (fun z => initialValueCurve G T x (ζ z.1) z.2) (V ×ˢ Icc 0 d) := by
  let V := U ∩ Φ ⁻¹' A
  have hV : IsOpen V := hΦ.continuousOn.isOpen_inter_preimage hU hA
  have hzV : z₀ ∈ V := ⟨hz₀, hcenter⟩
  have hVU : V ⊆ U := inter_subset_left
  have hr : 0 < r := hl.trans_lt hlr
  have hd : 0 < d := hr.trans hrd
  let ψ : E × ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun z => Ψ (Φ z.1, z.2)
  have hψ : ContDiffOn ℝ ∞ ψ (V ×ˢ Icc l d) := hΨ.comp
    (((hΦ.mono hVU).comp contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd)
    (fun _ hz => ⟨hz.1.2, hz.2⟩)
  obtain ⟨β, hβ, hβclock, hβcoord⟩ := exists_smooth_gaugeLift_of_maps
    ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) b t₀ x₀
    (S := V ×ˢ Icc l d) (c := fun z => T - z.2 ^ 2) (q := fun z => (ψ z).1)
    (contMDiffOn_const.sub (contMDiffOn_snd.pow 2)) (fun z hz => htime z.2 hz.2)
    (by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hψ.fst.contMDiffOn)
    (fun z hz => ((hdata (Φ z.1) hz.1.2).2 z.2 hz.2).1)
  have hCr : M14SqrtParameterInterval 0 (r ^ 2) = Icc 0 r := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hr.le]
  have hCd : M14SqrtParameterInterval 0 (d ^ 2) = Icc 0 d := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hd.le]
  have hpaths (z : E) (hz : z ∈ V) :
      ∃ y : G.Point, ∃ Q : M14SquareRootInitialValuePath G T (d ^ 2) x y (ζ z),
        EqOn Q.square_path.curve (fun s => (G.gaugeCover.cylinder b).toSpacetime (β (z, s)))
          (Icc l d) := by
    obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hr).mp (hsurv z hz.1)
    have hβ₀z : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞
        (fun s => β₀ (z, s)) (Icc l r) := hβ₀.comp
      (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hs => ⟨hz.1, hs⟩)
    have hrec (s : ℝ) (hs : s ∈ Icc l r) :
        (G.gaugeCover.cylinder b).toSpacetime (β₀ (z, s)) = P.square_path.curve s := by
      have hsP : s ∈ M14SqrtParameterInterval 0 (r ^ 2) := hCr ▸ ⟨hl.trans hs.1, hs.2⟩
      exact (hrec₀ (z, s) ⟨hz.1, hs⟩).trans
        (initialValueCurve_eqOn_square hM04 hM12 P hsP)
    have hψz : ContDiffOn ℝ ∞ (fun s => ψ (z, s)) (Icc l d) :=
      hψ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hs => ⟨hz, hs⟩)
    exact exists_initialValuePath_realizing_phase_continuation hM04 hM12 b W t₀ x₀
      hl hlr hrd P (fun s => β₀ (z, s)) hβ₀z hrec htime
      (fun s => ψ (z, s)) hψz
      (fun s hs => ((hdata (Φ z) hz.2).2 s hs).1)
      (fun s hs => ((hdata (Φ z) hz.2).2 s hs).2)
      (((hdata (Φ z) hz.2).1).trans (hi z hz.1)) (fun s => β (z, s))
      (fun s hs => hβclock (z, s) ⟨hz, hs⟩) (fun s hs => hβcoord (z, s) ⟨hz, hs⟩)
  refine ⟨V, hV, hzV, hVU, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, Q, _⟩ := hpaths z.1 hz.1
    exact initialValueDomain_prefix (Or.inr ⟨hd, y, ⟨Q⟩⟩) hz.2.1 hz.2.2
  · apply contMDiffOn_union_closed_tubes (spacetimeModel n) hlr
      (hγ.mono (prod_mono hVU (Subset.refl _)))
    apply ((G.gaugeCover.cylinder b).smooth.comp_contMDiffOn hβ).congr
    intro z hz
    obtain ⟨_, Q, hQ⟩ := hpaths z.1 hz.1
    have hsQ : z.2 ∈ M14SqrtParameterInterval 0 (d ^ 2) :=
      hCd ▸ ⟨hl.trans hz.2.1, hz.2.2⟩
    exact (initialValueCurve_eqOn_square hM04 hM12 Q hsQ).trans (hQ hz.2)

end PoincareConjecture.M14
