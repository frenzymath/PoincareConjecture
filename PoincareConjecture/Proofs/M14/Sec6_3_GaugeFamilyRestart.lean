import PoincareConjecture.Proofs.M14.Sec6_3_FamilyContinuation
import PoincareConjecture.Proofs.M14.Sec6_3_FamilyMomentum
import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyNeighborhood

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 800000 in

theorem initialValueCurve_smooth_tube_of_gauge_restart
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {T a r d : ℝ} (ha : 0 ≤ a) (har : a < r) (hrd : r < d)
    {x : G.Point} (ζ : E → G.Horizontal x) {U : Set E} (hU : IsOpen U)
    {z₀ : E} (hz₀ : z₀ ∈ U)
    (hγ : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z => initialValueCurve G T x (ζ z.1) z.2) (U ×ˢ Icc 0 r))
    (hsurv : ∀ z ∈ U, (ζ z, r) ∈ initialValueDomain G T x)
    {N : Set G.Point} (hN : IsOpen N) (hcentral : initialValueCurve G T x (ζ z₀) r ∈ N)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift N)
    (hrec : ∀ p ∈ N, (G.gaugeCover.cylinder b).toSpacetime (lift p) = p)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞
      (fun s => lift (initialValueCurve G T x (ζ z₀) s)) (Icc a d))
    (htime : ∀ s ∈ Icc a d, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))} (hA : IsOpen A)
    (hcenter : ((lift (initialValueCurve G T x (ζ z₀) r)).2.val,
      M08.chartMomentumVector (M08.chartActionMetric W.flow T x₀
        (r, (lift (initialValueCurve G T x (ζ z₀) r)).2.val))
        (derivWithin (fun s => (lift (initialValueCurve G T x (ζ z₀) s)).2.val)
          (Icc a d) r)) ∈ A)
    (Ψ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hΨ : ContDiffOn ℝ ∞ Ψ (A ×ˢ Icc a d))
    (hdata : ∀ y ∈ A, Ψ (y, r) = y ∧ ∀ s ∈ Icc a d,
      (Ψ (y, s)).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
        HasDerivWithinAt (fun t => Ψ (y, t))
          (M08.closedChartEulerPhase W.flow T x₀ (Icc a d) s (Ψ (y, s))) (Icc a d) s) :
    ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      (∀ z ∈ V ×ˢ Icc 0 d, (ζ z.1, z.2) ∈ initialValueDomain G T x) ∧
      ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
        (fun z => initialValueCurve G T x (ζ z.1) z.2) (V ×ˢ Icc 0 d) := by
  let γ : E × ℝ → G.Point := fun z => initialValueCurve G T x (ζ z.1) z.2
  have hsmall := hγ.mono (prod_mono (Subset.refl U) (Icc_subset_Icc ha le_rfl))
  have hnear : γ ⁻¹' N ∈ 𝓝[U ×ˢ Icc a r] (z₀, r) :=
    (hsmall.continuousOn (z₀, r) ⟨hz₀, har.le, le_rfl⟩).preimage_mem_nhdsWithin
      (hN.mem_nhds hcentral)
  obtain ⟨V, hV, hzV, hVU, l, c, hal, hlr, hrc, hcr, hmap, _⟩ :=
    exists_open_closed_family_neighborhood hU hz₀ har le_rfl hnear
  have hc : c = r := le_antisymm hcr hrc
  subst c
  let β₀ := lift ∘ γ
  have hβ₀ : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β₀
      (V ×ˢ Icc l r) := hlift.comp
    (hγ.mono (prod_mono hVU (Icc_subset_Icc (ha.trans hal.le) le_rfl))) hmap
  have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
    contMDiff_subtype_val
  have hq : ContDiffOn ℝ ∞ (fun z => (β₀ z).2.val) (V ×ˢ Icc l r) := by
    have h := hval.comp_contMDiffOn (fun z hz => (hβ₀ z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  have hsrc (z : E × ℝ) : (β₀ z).2.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have heq : extChartAt (𝓡 n) x₀ (β₀ z).2 = (β₀ z).2.val := by
      rw [extChartAt_coe]
      rfl
    rw [← heq]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  let Φ := fun z => ((β₀ (z, r)).2.val,
    M08.chartMomentumVector (M08.chartActionMetric W.flow T x₀ (r, (β₀ (z, r)).2.val))
      (derivWithin (fun s => (β₀ (z, s)).2.val) (Icc l r) r))
  have hsub : Icc l r ⊆ Icc a d := Icc_subset_Icc hal.le hrd.le
  have hΦ : ContDiffOn ℝ ∞ Φ V := closedChartFamily_initialPhase_contDiffOn W.flow T x₀
    hV (uniqueDiffOn_Icc hlr) (fun s hs => htime s (hsub hs)) _ hq
    (fun z _ => hsrc z) ⟨hlr.le, le_rfl⟩
  have hqcentral := gaugeLift_spatialCurve_contDiffOn b hβ
  have hdq := derivWithin_subset hsub (uniqueDiffOn_Icc hlr r ⟨hlr.le, le_rfl⟩)
    ((hqcentral r ⟨har.le, hrd.le⟩).differentiableWithinAt (by simp))
  have hΦcenter : Φ z₀ ∈ A := by
    dsimp only [Φ, β₀, γ, Function.comp_def]
    rw [hdq]
    exact hcenter
  have htail : Icc l d ⊆ Icc a d := Icc_subset_Icc hal.le le_rfl
  obtain ⟨V', hV', hzV', hV'V, hsurv', hsmooth⟩ := initialValueCurve_smooth_tube_of_restart
    hM04 hM12 b W t₀ x₀ (ha.trans hal.le) hlr hrd ζ hV hzV
    (hγ.mono (prod_mono hVU (Subset.refl _))) (fun z hz => hsurv z (hVU hz))
    β₀ hβ₀ (fun z hz => hrec (γ z) (hmap hz)) (fun s hs => htime s (htail hs))
    Φ hΦ (fun _ _ => rfl) hA hΦcenter Ψ (hΨ.mono (prod_mono (Subset.refl _) htail))
    (by
      intro y hy
      refine ⟨(hdata y hy).1, ?_⟩
      intro s hs
      obtain ⟨hchart, hderiv⟩ := (hdata y hy).2 s (htail hs)
      refine ⟨hchart, ?_⟩
      rw [closedChartEulerPhase_restrict W.flow hM04 T x₀ htime htail hs hchart]
      exact hderiv.mono htail)
  exact ⟨V', hV', hzV', hV'V.trans hVU, hsurv', hsmooth⟩

end PoincareConjecture.M14
