import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FlowConvergence
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinQuotientFlow
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinSourceExhaustion
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SourceEmbeddings
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.ChosenChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem exists_partial_flow_limit_of_within_spacetime_bounds
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    (hconvU : ∀ i, Convex ℝ (U i)) [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    {i₀ : ℕ} (p : Piece U i₀) (A : ℝ) (hA : 0 < A)
    (hrange : ∀ i (x : Piece U i), D i₀ i (p, x) < A)
    (hcover : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ℕ,
      ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hconvJ : Convex ℝ J)
    [LocallyCompactSpace J] (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (Fseq : ∀ k, RicciFlow n (M k) J)
    (hdist : ∀ k (x y : M k), edist x y = ((Fseq k).metric t₀).edist x y)
    (hjets : ∀ i (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ m
          (fun w : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric w.1).pullbackCoefficients
              (chartParametrization U hU (e k i)) w.2) (J ×ˢ U i) z‖ ≤ C)
    (hpositive : ∀ t ∈ J, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤
        ((Fseq k).metric t).pullbackCoefficients (chartParametrization U hU (e k i)) x v v) :
    Nonempty (M28.PartialPointedFlowConvergence Fseq (fun k => e k i₀ p) A t₀) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let : ∀ i, LocallyCompactSpace (J ×ˢ U i) := fun i =>
    (Homeomorph.Set.prod J (U i)).isOpenEmbedding.locallyCompactSpace
  let hp := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let hO := overlapSystem_smooth U hU hp L he c hc hlower hopen hconn hsmooth hbound
  let hclosed := overlapSystem_closed hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  obtain ⟨ρ, hρ, _, B, hBsmooth, hBjets, gLimit, hcompat, hcoeff, _, FQ, hFQ⟩ :=
    exists_quotientRicciFlow_of_within_spacetime_bounds U hU hconvU hp L he c hc
      hlower hopen hconn hsmooth hJ hconvJ t₀ ht₀ Fseq hjets hpositive hbound
  have hDρ : ∀ i j, TendstoLocallyUniformly
      (fun k (q : Piece U i × Piece U j) => dist (e (ρ k) i q.1) (e (ρ k) j q.2))
      (D i j) atTop := by
    intro i j W hW x
    obtain ⟨N, hN, heventual⟩ := hD i j W hW x
    exact ⟨N, hN, hρ.tendsto_atTop.eventually heventual⟩
  have hboundρ : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e (ρ k) j) (e (ρ k) i x))) := by
    intro i j K hK hKU m
    obtain ⟨C, hC⟩ := hbound i j K hK hKU m
    exact ⟨C, hρ.tendsto_atTop.eventually hC⟩
  have hcoverρ : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ℕ,
      ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e (ρ k) i₀ p) R ⊆ ⋃ i ∈ s, e (ρ k) i '' K i := by
    intro R hR hRA
    obtain ⟨s, K, hK, hcoverK⟩ := hcover R hR hRA
    exact ⟨s, K, hK, hρ.tendsto_atTop.eventually hcoverK⟩
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, σ, hσ,
      f, hf, happrox, hreadout, hboundary⟩ :=
    exists_partial_pointed_source_exhaustion U hU hDρ L (fun k => he (ρ k)) c hc
      (fun k => hlower (ρ k)) (fun k => hopen (ρ k)) (fun k => hconn (ρ k))
      (fun k => hsmooth (ρ k)) hboundρ p A hA hrange hcoverρ
  let : ConnectedSpace (Quotient O.setoid) := hconnected
  let C := O.flowCarrier U hU hO hclosed
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  have hsourceJets := source_exhaustion_spacetime_pullbackCoefficients_tendsto_withinJets
    U hU O hO hE hEmono hEcover f (fun k => (hf k).2.1)
    L (fun k => he (ρ (σ k))) c hc (fun k => hlower (ρ (σ k)))
    (fun k => hopen (ρ (σ k))) (fun k => hconn (ρ (σ k)))
    (fun k => hsmooth (ρ (σ k))) happrox hreadout hJ hconvJ
    (fun k => (Fseq (ρ (σ k))).metric) (fun k => (Fseq (ρ (σ k))).smooth)
    B hBsmooth (fun i m K hK hKU W hW =>
      hσ.tendsto_atTop.eventually (hBjets i m K hK hKU W hW))
  have hlimit (i : ℕ) : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (FQ.metric z.1).pullbackCoefficients (chartParametrization U hU (O.include i)) z.2)
      (B i) (J ×ˢ U i) := by
    intro z hz
    rw [hFQ]
    exact quotientMetric_pullbackCoefficients_eqOn U hU O hO (gLimit z.1)
      (hcompat z.1) (fun i x => B i (z.1, x)) (hcoeff z.1 hz.1) i hz.2
  have hsource (i k : ℕ) : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq (ρ k)).metric z.1).pullbackCoefficients
          (chartParametrization U hU (e (ρ k) i)) z.2) (J ×ˢ U i) :=
    (Fseq (ρ k)).smooth.contDiffOn_spacetime_pullbackCoefficients_within (hU i)
      (contMDiffOn_chartParametrization U hU (hsmooth (ρ k) i).contMDiff)
  have hBspatial : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((Fseq (ρ k)).metric t₀).pullbackCoefficients
          (chartParametrization U hU (e (ρ k) i))))
      (iteratedFDeriv ℝ m (fun x => B i (t₀, x))) atTop K := by
    intro i m K hK hKU
    have hKS : (fun x : EuclideanSpace ℝ (Fin n) => (t₀, x)) '' K ⊆ J ×ˢ U i := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨ht₀, hKU hx⟩
    have hj := hBjets i m _ (hK.image (continuous_const.prodMk continuous_id)) hKS
    have hjet := hj.iteratedFDeriv_spatial_slice hJ (hU i) hKS
        (Eventually.of_forall (hsource i)) (hBsmooth i)
        (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
    exact (hjet.comp (fun x => (t₀, x))).mono (fun x hx => mem_image_of_mem _ hx)
  have hBspatialSmooth (i : ℕ) : ContDiffOn ℝ ∞ (fun x => B i (t₀, x)) (U i) :=
    (hBsmooth i).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ hx => ⟨ht₀, hx⟩)
  have hspatialJets := source_exhaustion_pullbackCoefficients_tendsto_jets
    U hU O hO hE hEmono hEcover f (fun k => (hf k).2.1)
    L (fun k => he (ρ (σ k))) c hc (fun k => hlower (ρ (σ k)))
    (fun k => hopen (ρ (σ k))) (fun k => hconn (ρ (σ k)))
    (fun k => hsmooth (ρ (σ k))) happrox hreadout
    (fun k => (Fseq (ρ (σ k))).metric t₀) (fun i x => B i (t₀, x)) hBspatialSmooth
    (fun i m K hK hKU W hW => hσ.tendsto_atTop.eventually (hBspatial i m K hK hKU W hW))
  refine ⟨{
    limitCarrier := C
    limitMetric := FQ.metric t₀
    base := O.include i₀ p
    subsequence := ρ ∘ σ
    subsequence_strictMono := hρ.comp hσ
    exhaustion := E
    exhaustion_open := hE
    exhaustion_connected := hEc
    base_in_exhaustion := hEp
    exhaustion_compactClosure := hEK
    exhaustion_step := hEstep
    exhaustion_covers := hEcover
    embedding := f
    embedding_open := fun k => (hf k).1
    embedding_smooth := fun k => (hf k).2.1
    base_preserving := fun k => (hf k).2.2
    metric_jets := ?_
    boundary_control := ?_
    baseTime_mem := ht₀
    limitFlow := FQ
    metric_at_baseTime := rfl
    spacetime_metric_jets := ?_ }⟩
  · intro q m K hK hKchart
    obtain ⟨i, _, htarget, hinverse⟩ := exists_chosen_quotient_chart U hU O q
    have hKU : K ⊆ U i := by simpa only [htarget] using hKchart
    rw [hinverse]
    have hlim : EqOn
        ((FQ.metric t₀).pullbackCoefficients (chartParametrization U hU (O.include i)))
        (fun x => B i (t₀, x)) (U i) := by
      intro x hx
      exact hlimit i (x := (t₀, x)) ⟨ht₀, hx⟩
    exact (hspatialJets i m K hK hKU).congr_right
      ((eqOn_iteratedFDeriv_of_isOpen (hU i) hlim m).symm.mono hKU)
  · intro R hR
    obtain ⟨l, hl⟩ := hboundary R hR
    exact ⟨l, hl.mono fun j hj q hq => by
      simpa only [Function.comp_apply, hdist] using hj q hq⟩
  · intro q m K hK hKchart
    obtain ⟨i, _, htarget, hinverse⟩ := exists_chosen_quotient_chart U hU O q
    have hKU : K ⊆ J ×ˢ U i := by simpa only [htarget] using hKchart
    rw [hinverse, htarget]
    exact (hsourceJets i m K hK hKU).congr_right
      (((hlimit i).iteratedFDerivWithin m).symm.mono hKU)

end PoincareConjecture.ChartDistance
