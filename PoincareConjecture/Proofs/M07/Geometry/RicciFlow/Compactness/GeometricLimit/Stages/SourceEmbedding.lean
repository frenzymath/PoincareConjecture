import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceSeparation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.BoundaryEscape
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.M07.Topology.Gluing.Embedding

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
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
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in
theorem exists_two_chart_source_embeddings
    (hbound : ∀ i j, Poincare.Analysis.Calculus.LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {A : Set (Piece U i)} {C : Set (Piece U j)}
    (hA : IsCompact A) (hC : IsCompact C) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))) L he c hc hlower hopen hconn
    letI := quotientChartedSpace U hU O
    let qi : interior A → Quotient O.setoid := fun x => O.include i x
    let qj : interior C → Quotient O.setoid := fun y => O.include j y
    ∃ a : ℕ → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      (∀ m B, IsCompact B → TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
        (iteratedFDeriv ℝ m id) atTop B) ∧
      ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
        ∃ F : Quotient O.setoid → M k,
          Topology.IsOpenEmbedding (fun x : (range qi ∪ range qj : Set (Quotient O.setoid)) => F x) ∧
          IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ F (range qi ∪ range qj) ∧
          (∀ x, F (qi x) = e k i x) ∧
          (∀ y, F (qj y) =
            chartParametrization U hU (e k j) (a k (y : Piece U j))) := by
  classical
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  let : ∀ l, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U l) :=
    fun l => (hU l).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hO := overlapSystem_smooth U hU hp L he c hc hlower hopen hconn hsmooth hbound
  let qi : interior A → Quotient O.setoid := fun x => O.include i x
  let qj : interior C → Quotient O.setoid := fun y => O.include j y
  obtain ⟨S, _, _, a, ha, hjet⟩ :=
    exists_source_chart_corrections_with_exact_identifications U hU hD L he c hc hlower
      hopen hconn hsmooth hbound i j hA hC
  refine ⟨a, hjet, ?_⟩
  filter_upwards [ha] with k hk
  let b : Piece U j ≃ₜ Piece U j := ((a k).image (U j)).trans
    (Homeomorph.setCongr hk.2.2.2.1)
  have hb (y : Piece U j) : e k j (b y) = chartParametrization U hU (e k j) (a k y) := by
    have hby : (b y : EuclideanSpace ℝ (Fin n)) = a k y := rfl
    rw [← hby, chartParametrization_apply]
  let ad : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toEquiv := (a k).toEquiv
      contMDiff_toFun := hk.1.contMDiff
      contMDiff_invFun := hk.2.1.contMDiff }
  have hblocal : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ b := by
    intro y
    have hy := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) (U j) (hU j) ∞ y
    have hby := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) (U j) (hU j) ∞ (b y)
    have hac := hy.comp (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (ad.isLocalDiffeomorph (y : EuclideanSpace ℝ (Fin n)))
    have hinv : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hby.localInverse (ad y) :=
      hby.localInverse_isLocalDiffeomorphAt
    apply (hac.comp (𝓡 n) (Piece U j) hinv).congr_of_eventuallyEq
    filter_upwards [b.continuous.continuousAt.preimage_mem_nhds
      (hby.localInverse.open_target.mem_nhds hby.localInverse_mem_target)] with z hz
    exact (hby.localInverse_left_inv hz).symm
  have hqi : Topology.IsOpenEmbedding qi :=
    (O.include_isOpenEmbedding i).comp isOpen_interior.isOpenEmbedding_subtypeVal
  have hqj : Topology.IsOpenEmbedding qj :=
    (O.include_isOpenEmbedding j).comp isOpen_interior.isOpenEmbedding_subtypeVal
  have hei := (hopen k i).comp (isOpen_interior (s := A)).isOpenEmbedding_subtypeVal
  have hej := ((hopen k j).comp b.isOpenEmbedding).comp
    (isOpen_interior (s := C)).isOpenEmbedding_subtypeVal
  obtain ⟨F, hF, hFi, hFj⟩ := exists_isOpenEmbedding_union_ranges hqi hqj hei hej (fun x y => by
    change e k i x = e k j (b y) ↔ O.include i x = O.include j y
    rw [hb, hk.2.2.2.2 x (interior_subset x.property) y (interior_subset y.property)]
    exact (zero_iff_transition hp c hc hlower).trans (O.include_eq_iff i j x y).symm)
  let V := range qi ∪ range qj
  let F' : Quotient O.setoid → M k :=
    Function.extend (Subtype.val : V → Quotient O.setoid) F
      (fun _ => e k i Classical.ofNonempty)
  have hext (x : V) : F' x = F x := Subtype.val_injective.extend_apply F _ x
  have hleft (x : interior A) : F' (qi x) = e k i x :=
    (hext ⟨qi x, Or.inl (mem_range_self x)⟩).trans (hFi x)
  have hright (y : interior C) : F' (qj y) = chartParametrization U hU (e k j) (a k (y : Piece U j)) :=
    (hext ⟨qj y, Or.inr (mem_range_self y)⟩).trans ((hFj y).trans (hb y))
  refine ⟨hk.1, hk.2.1, F', ?_, ?_, hleft, hright⟩
  · exact (funext hext).symm ▸ hF
  · rintro ⟨q, hq⟩
    rcases hq with (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · apply (include_isLocalDiffeomorph U hU O hO i x).of_comp
      apply (hsmooth k i (x : Piece U i)).congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds x.property] with z hz
      exact hleft ⟨z, hz⟩
    · apply (include_isLocalDiffeomorph U hU O hO j y).of_comp
      apply ((hblocal (y : Piece U j)).comp (𝓡 n) (M k)
        (hsmooth k j _)).congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds y.property] with z hz
      exact (hright ⟨z, hz⟩).trans (hb z).symm

include he in
omit [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)] in
theorem tendstoUniformlyOn_chartParametrization_displacement
    {j : ι} {C : Set (Piece U j)} (hC : IsCompact C)
    {a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (ha : TendstoUniformlyOn a id atTop (Subtype.val '' C)) :
    TendstoUniformlyOn
      (fun k (y : Piece U j) => dist (chartParametrization U hU (e k j) (a k y)) (e k j y))
      (fun _ => 0) atTop C := by
  obtain ⟨T, _, hTU, hT⟩ :=
    Poincare.Analysis.Calculus.exists_compact_target_of_tendstoUniformlyOn
      (hC.image continuous_subtype_val) (hU j) continuous_id.continuousOn
      (by rintro _ ⟨y, _, rfl⟩; exact y.property) ha
  let b : ℕ → Piece U j → Piece U j := fun k y =>
    (hU j).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm (a k y)
  have hbval : ∀ᶠ k in atTop, ∀ y ∈ C,
      (b k y : EuclideanSpace ℝ (Fin n)) = a k y := by
    filter_upwards [hT] with k hk y hy
    exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (f := (Subtype.val : Piece U j → EuclideanSpace ℝ (Fin n)))
      (h := (hU j).isOpenEmbedding_subtypeVal)
      ⟨⟨a k y, hTU (hk (mem_image_of_mem Subtype.val hy))⟩, rfl⟩
  have hb : TendstoUniformlyOn b id atTop C := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hbval, Metric.tendstoUniformlyOn_iff.mp ha ε hε] with k hk hsmall y hy
    change dist (y : EuclideanSpace ℝ (Fin n)) (b k y : EuclideanSpace ℝ (Fin n)) < ε
    rw [hk y hy]
    exact hsmall y (mem_image_of_mem Subtype.val hy)
  exact tendstoUniformlyOn_source_displacement_of_corrections (fun k => he k j) hb

include hD he hc hlower hopen hconn hsmooth in

theorem exists_two_chart_source_embedding_sequence
    (hbound : ∀ i j, Poincare.Analysis.Calculus.LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {A : Set (Piece U i)} {C : Set (Piece U j)}
    (hA : IsCompact A) (hC : IsCompact C) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))) L he c hc hlower hopen hconn
    letI := quotientChartedSpace U hU O
    let V := O.include i '' interior A ∪ O.include j '' interior C
    ∃ F : ∀ k, Quotient O.setoid → M k,
      (∀ᶠ k in atTop,
        Topology.IsOpenEmbedding (fun x : V => F k x) ∧
        IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V ∧
        ∀ x ∈ A, F k (O.include i x) = e k i x) ∧
      ∀ l K, IsCompact K →
        O.include l '' K ⊆ O.include i '' A ∪ O.include j '' C →
        TendstoUniformlyOn (fun k x => dist (F k (O.include l x)) (e k l x))
          (fun _ => 0) atTop K := by
  classical
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  let (k : ℕ) : Nonempty (M k) := ⟨e k i Classical.ofNonempty⟩
  obtain ⟨A', hA', hAA'⟩ := exists_compact_superset hA
  obtain ⟨C', hC', hCC'⟩ := exists_compact_superset hC
  obtain ⟨a, ha, hmaps⟩ := exists_two_chart_source_embeddings U hU hD L he c hc hlower
    hopen hconn hsmooth hbound i j hA' hC'
  have hmaps' := hmaps.mono fun _ hk => hk.2.2
  obtain ⟨F, hF⟩ := Filter.skolem.mp hmaps'
  let V := O.include i '' interior A ∪ O.include j '' interior C
  let V' := O.include i '' interior A' ∪ O.include j '' interior C'
  have hr (l : ι) (B : Set (Piece U l)) :
      range (fun x : B => O.include l x) = O.include l '' B := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_image_of_mem _ x.property
    · rintro ⟨x, hx, rfl⟩
      exact mem_range_self (⟨x, hx⟩ : B)
  have hranges : (range (fun x : interior A' => O.include i x) ∪
      range (fun y : interior C' => O.include j y)) = V' := by
    rw [hr, hr]
  have hV : IsOpen V := (O.include_isOpenMap i _ isOpen_interior).union
    (O.include_isOpenMap j _ isOpen_interior)
  have hVV' : V ⊆ V' := union_subset_union
    (image_mono (interior_subset.trans hAA')) (image_mono (interior_subset.trans hCC'))
  have hleft : ∀ᶠ k in atTop, ∀ x ∈ A, F k (O.include i x) = e k i x :=
    hF.mono fun k hk x hx => hk.2.2.1 ⟨x, hAA' hx⟩
  have hright : ∀ᶠ k in atTop, ∀ y ∈ C, F k (O.include j y) =
      chartParametrization U hU (e k j) (a k y) :=
    hF.mono fun k hk y hy => hk.2.2.2 ⟨y, hCC' hy⟩
  have hzero : TendstoUniformlyOn (fun k => (a k : _ → _)) id atTop (Subtype.val '' C) := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
          (ha 0 _ (hC.image continuous_subtype_val))
  have happroxC := tendstoUniformlyOn_chartParametrization_displacement U hU L he hC hzero
  have happroxC' : TendstoUniformlyOn
      (fun k y => dist (F k (O.include j y)) (e k j y)) (fun _ => 0) atTop C := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hright, Metric.tendstoUniformlyOn_iff.mp happroxC ε hε] with k hk heps y hy
    rw [hk y hy]
    exact heps y hy
  have happroxA : TendstoUniformlyOn
      (fun k x => dist (F k (O.include i x)) (e k i x)) (fun _ => 0) atTop A := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hleft] with k hk x hx
    simpa only [hk x hx, dist_self] using hε
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [hF, hleft] with k hk hl
    have hemb : Topology.IsOpenEmbedding (fun x : V' => F k x) := by
      have h := hk.1
      change Topology.IsOpenEmbedding (fun x : (range (fun x : interior A' => O.include i x) ∪
        range (fun y : interior C' => O.include j y) : Set (Quotient O.setoid)) => F k x) at h
      exact h.comp (Homeomorph.setCongr hranges.symm).isOpenEmbedding
    have hlocal : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V' := by
      have h := hk.2.1
      change IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k)
        (range (fun x : interior A' => O.include i x) ∪
          range (fun y : interior C' => O.include j y)) at h
      rwa [hranges] at h
    refine ⟨hemb.comp (.inclusion hVV' (hV.preimage continuous_subtype_val)), ?_, hl⟩
    intro x
    exact hlocal ⟨x, hVV' x.property⟩
  · intro l K hK hcover
    let b : Bool → ι := fun t => if t then j else i
    let B : ∀ t, Set (Piece U (b t)) := fun t => Bool.casesOn t A C
    apply tendstoUniformlyOn_chart_approximation_of_finite_cover hD O
      (fun l q x y => (zero_iff_transition hp c hc hlower).symm)
      Finset.univ b B (fun t _ => by cases t <;> assumption)
      (fun t _ => by cases t <;> assumption) hK
    intro q hq
    rcases hcover hq with hi | hj
    · exact mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨Finset.mem_univ _, hi⟩⟩
    · exact mem_iUnion.mpr ⟨true, mem_iUnion.mpr ⟨Finset.mem_univ _, hj⟩⟩

end PoincareConjecture.ChartDistance
