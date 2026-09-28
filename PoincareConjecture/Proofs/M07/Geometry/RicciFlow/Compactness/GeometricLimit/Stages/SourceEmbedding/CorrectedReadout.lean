import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Readout
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]

theorem exists_eventual_corrected_readout_eqOn
    {i j : ι} (τ : OpenPartialHomeomorph (Piece U i) (Piece U j))
    {Q : Type*} (qi : Piece U i → Q) (qj : Piece U j → Q)
    (hq : ∀ x ∈ τ.source, qi x = qj (τ x))
    {N : Set (Piece U j)} (hN : IsOpen N)
    {x : Piece U i} (hx : x ∈ τ.source) (hxN : τ x ∈ N)
    {M : ℕ → Type*} {e : ∀ k l, Piece U l → M k}
    {F : ∀ k, Q → M k}
    {a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : ∀ᶠ k in atTop, ∀ y ∈ N,
      F k (qj y) = chartParametrization U hU (e k j) (a k y)) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧
      (x : EuclideanSpace ℝ (Fin n)) ∈ W ∧ W ⊆ Subtype.val '' τ.source ∧
      ∀ᶠ k in atTop, EqOn
        (coordinateRepresentative U hU (fun z => Function.invFun (e k i) (F k (qi z))))
        (coordinateRepresentative U hU (fun y => Function.invFun (e k i) (e k j y)) ∘
          (a k ∘ coordinateRepresentative U hU τ)) W := by
  let V := τ.source ∩ τ ⁻¹' N
  have hV : IsOpen V := τ.continuousOn.isOpen_inter_preimage τ.open_source hN
  refine ⟨Subtype.val '' V, (hU i).isOpenEmbedding_subtypeVal.isOpenMap _ hV,
    mem_image_of_mem Subtype.val ⟨hx, hxN⟩, image_mono inter_subset_left, ?_⟩
  filter_upwards [hF] with k hk z hz
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [Function.comp_apply, coordinateRepresentative_apply]
  rw [hq y hy.1, hk (τ y) hy.2]
  rfl

variable {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
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

theorem corrected_source_readout_smooth_convergence
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι)
    {a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hasmooth : ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k))
    (hajet : ∀ m K, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
        (iteratedFDeriv ℝ m id) atTop K) :
    let V := Subtype.val '' overlap (fun i j => D i j) i j
    let τ := coordinateRepresentative U hU (transition (fun i j => D i j) i j)
    let f := fun k => coordinateRepresentative U hU
      (fun y => Function.invFun (e k i) (e k j y))
    (∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ (a k ∘ τ)) W) ∧
    ∀ m K, IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k ∘ (a k ∘ τ)))
        (iteratedFDeriv ℝ m id) atTop K := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  have hopen' (l q : ι) : IsOpen (Subtype.val '' overlap (fun l q => D l q) l q) :=
    (hU l).isOpenEmbedding_subtypeVal.isOpenMap _
      (isOpen_overlap hp L he c hc hlower hopen hconn l q)
  have hs (l q : ι) : ContDiffOn ℝ ∞
      (coordinateRepresentative U hU (transition (fun l q => D l q) l q))
      (Subtype.val '' overlap (fun l q => D l q) l q) :=
    contDiffOn_of_locally_eventually_smooth
      (fun _ hx => coordinate_source_transition_tendsto U hU hp L he c hc hlower
        hopen hconn l q hx)
      (fun _ hx => exists_eventually_contDiffOn_coordinate_source_transition U hU hp
        L he c hc hlower hopen hconn hsmooth l q hx) (hbound l q)
  apply source_readout_smooth_convergence (hopen' i j) (hopen' j i) (hs i j) (hs j i)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨transition (fun l q => D l q) i j x, transition_mem hp hx,
      (coordinateRepresentative_apply U hU _ x).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, coordinateRepresentative_apply, id_eq,
      transition_inverse hp c hc hlower hx]
  · intro x hx
    obtain ⟨W, hW, hxW, _, hWs⟩ :=
      exists_eventually_contDiffOn_coordinate_source_transition U hU hp L he c hc hlower
        hopen hconn hsmooth j i hx
    exact ⟨W, hW, hxW, hWs⟩
  · intro m K hK hKV
    exact tendstoUniformlyOn_coordinate_source_transition_jet U hU hp L he c hc hlower
      hopen hconn hsmooth j i (hbound j i) m hK hKV
  · exact hasmooth
  · exact hajet

end PoincareConjecture.ChartDistance
