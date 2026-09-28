import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.LocalModels
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.CorrectedReadout

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2))
      (D i j) atTop)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in

theorem local_source_models_readout_smooth_convergence
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x)))) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
      L he c hc hlower hopen hconn
    ∀ {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)},
      IsOpen V → HasLocalSourceModels U hU O e F V → ∀ i,
      let Ω := Subtype.val '' (O.include i ⁻¹' V)
      let r := fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k i) (F k (O.include i x)))
      (∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧
        ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (r k) W) ∧
      ∀ m K, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (r k))
          (iteratedFDeriv ℝ m id) atTop K := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  dsimp only
  intro F V hV hmodels i
  let Ω := Subtype.val '' (O.include i ⁻¹' V)
  let r := fun k => coordinateRepresentative U hU
    (fun x => Function.invFun (e k i) (F k (O.include i x)))
  have hΩ : IsOpen Ω := (hU i).isOpenEmbedding_subtypeVal.isOpenMap _
    (hV.preimage (O.include_isOpenEmbedding i).continuous)
  have hlocal : ∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧
      ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        (∀ᶠ k in atTop, EqOn (r k) (g k) W) ∧
        (∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W) ∧
        ∀ m K, IsCompact K → K ⊆ W →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (g k))
            (iteratedFDeriv ℝ m id) atTop K := by
    rintro _ ⟨x, hxV, rfl⟩
    obtain ⟨j, B, hB, hqB, _, a, ha, haj, hformula⟩ :=
      hmodels (O.include i x) hxV
    obtain ⟨y, hyB, hyx⟩ := hqB
    have hxy := (O.include_eq_iff i j x y).mp hyx.symm
    obtain ⟨W₀, hW₀, hxW₀, hW₀overlap, heq⟩ :=
      exists_eventual_corrected_readout_eqOn U hU (O.transition i j)
        (O.include i) (O.include j)
        (fun z hz => (O.include_eq_iff i j z _).mpr ⟨hz, rfl⟩)
        hB hxy.1 (hxy.2.symm ▸ hyB) hformula
    obtain ⟨hgsmooth, hgjet⟩ := corrected_source_readout_smooth_convergence
      U hU hD L he c hc hlower hopen hconn hsmooth hbound i j ha haj
    obtain ⟨W₁, hW₁, hxW₁, _, hW₁smooth⟩ :=
      hgsmooth x (mem_image_of_mem Subtype.val hxy.1)
    let W := (W₀ ∩ W₁) ∩ Ω
    let g := fun k => coordinateRepresentative U hU
      (fun y => Function.invFun (e k i) (e k j y)) ∘
        (a k ∘ coordinateRepresentative U hU (transition (fun l q => D l q) i j))
    refine ⟨W, (hW₀.inter hW₁).inter hΩ,
      ⟨⟨hxW₀, hxW₁⟩, mem_image_of_mem Subtype.val hxV⟩,
      inter_subset_right, g, ?_, ?_, ?_⟩
    · exact heq.mono fun k hk => hk.mono (fun _ hz => hz.1.1)
    · exact hW₁smooth.mono fun k hk => hk.mono (fun _ hz => hz.1.2)
    · intro m K hK hKW
      exact hgjet m K hK (fun z hz => hW₀overlap (hKW hz).1.1)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨W, hW, hxW, hWΩ, g, heq, hsmooth, _⟩ := hlocal x hx
    refine ⟨W, hW, hxW, hWΩ, ?_⟩
    filter_upwards [heq, hsmooth] with k hk hks
    exact hks.congr hk
  · intro m K hK hKΩ
    apply tendstoUniformlyOn_iteratedFDeriv_of_local_models hΩ ?_ m hK hKΩ
    intro x hx
    obtain ⟨W, hW, hxW, hWΩ, g, heq, _, hgjet⟩ := hlocal x hx
    exact ⟨W, hW, hxW, hWΩ, g, id, heq, fun _ _ => rfl, hgjet⟩

end PoincareConjecture.ChartDistance
