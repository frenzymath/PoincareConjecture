import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Gluing
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceSmooth
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SmoothLimit
import PoincareConjecture.Proofs.M07.Geometry.Manifold.Gluing.Smooth








set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]

noncomputable def coordinateRepresentative {i j : ι} (f : Piece U i → Piece U j)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  f ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x)

@[simp] theorem coordinateRepresentative_apply {i j : ι}
    (f : Piece U i → Piece U j) (x : Piece U i) :
    coordinateRepresentative U hU f x = (f x : EuclideanSpace ℝ (Fin n)) := by
  simp [coordinateRepresentative, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

theorem contDiffOn_coordinateRepresentative {i j : ι} {f : Piece U i → Piece U j}
    {V : Set (Piece U i)}
    (hf : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ f V) :
    ContDiffOn ℝ ∞ (coordinateRepresentative U hU f) (Subtype.val '' V) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hinv := contMDiffOn_isOpenEmbedding_symm (I := 𝓡 n) (n := ∞)
    (hU i).isOpenEmbedding_subtypeVal
  have hval := contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞)
    (hU j).isOpenEmbedding_subtypeVal
  have hmap : MapsTo ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm)
      (Subtype.val '' V) V := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv] using hx
  exact (hval.comp_contMDiffOn
    (hf.comp (hinv.mono (image_subset_range _ _)) hmap)).contDiffOn

theorem contMDiffOn_of_coordinateRepresentative {i j : ι} {f : Piece U i → Piece U j}
    {V : Set (Piece U i)}
    (hf : ContDiffOn ℝ ∞ (coordinateRepresentative U hU f) (Subtype.val '' V)) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ f V := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hval := contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞)
    (hU i).isOpenEmbedding_subtypeVal
  have hcoord := hf.contMDiffOn.comp hval.contMDiffOn (mapsTo_image _ _)
  have hinv := contMDiffOn_isOpenEmbedding_symm (I := 𝓡 n) (n := ∞)
    (hU j).isOpenEmbedding_subtypeVal
  have hmap : MapsTo (fun x : Piece U i => coordinateRepresentative U hU f x)
      V (range (Subtype.val : Piece U j → EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    exact ⟨f x, (coordinateRepresentative_apply U hU f x).symm⟩
  apply (hinv.comp hcoord hmap).congr
  intro x hx
  simp only [Function.comp_apply, coordinateRepresentative_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_eq_coordinateRepresentative {i j : ι} {f : Piece U i → Piece U j}
    (x : Piece U i)
    (hf : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      MDifferentiableAt (𝓡 n) (𝓡 n) f x) :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ (coordinateRepresentative U hU f) x := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  rw [mfderiv, if_pos hf]
  change fderivWithin ℝ (coordinateRepresentative U hU f) (range id) x = _
  rw [range_id, fderivWithin_univ]

variable {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn in
omit [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] in
theorem coordinate_source_transition_tendsto (i j : ι)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Subtype.val '' overlap (fun i j => D i j) i j) :
    Tendsto (fun k => coordinateRepresentative U hU
      (fun y => Function.invFun (e k j) (e k i y)) x) atTop
      (𝓝 (coordinateRepresentative U hU (transition (fun i j => D i j) i j) x)) := by
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  obtain ⟨x, hx, rfl⟩ := hx
  simp only [coordinateRepresentative_apply]
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_source_transition hD L he c hc hlower hopen hconn hx)

include hD he hc hlower hopen hconn hsmooth in
theorem exists_eventually_contDiffOn_coordinate_source_transition (i j : ι)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Subtype.val '' overlap (fun i j => D i j) i j) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧
      V ⊆ Subtype.val '' overlap (fun i j => D i j) i j ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (coordinateRepresentative U hU (fun y => Function.invFun (e k j) (e k i y))) V := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨V, hV, hxV, hVoverlap, hVsmooth⟩ :=
    exists_eventually_smooth_source_transition hD L he c hc hlower hopen hconn hsmooth hx
  refine ⟨Subtype.val '' V, (hU i).isOpenEmbedding_subtypeVal.isOpenMap _ hV,
    mem_image_of_mem _ hxV, image_mono hVoverlap, ?_⟩
  exact hVsmooth.mono fun k hk => contDiffOn_coordinateRepresentative U hU hk

include hD he hc hlower hopen hconn hsmooth in
theorem overlapSystem_smooth
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x)))) :
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    SmoothOverlap U hU (overlapSystem hD L he c hc hlower hopen hconn) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  intro i j
  apply contMDiffOn_of_coordinateRepresentative U hU
  exact contDiffOn_of_locally_eventually_smooth
    (fun _ hx => coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn
      i j hx)
    (fun _ hx => exists_eventually_contDiffOn_coordinate_source_transition U hU hD L he c hc
      hlower hopen hconn hsmooth i j hx) (hbound i j)

include hD he hc hlower hopen hconn hsmooth in
theorem tendsto_coordinate_source_transition_jet (i j : ι)
    (hbound : LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (m : ℕ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Subtype.val '' overlap (fun i j => D i j) i j) :
    Tendsto (fun k => iteratedFDeriv ℝ m (coordinateRepresentative U hU
      (fun y => Function.invFun (e k j) (e k i y))) x) atTop
      (𝓝 (iteratedFDeriv ℝ m
        (coordinateRepresentative U hU (transition (fun i j => D i j) i j)) x)) :=
  tendsto_iteratedFDeriv_of_locally_eventually_smooth
    (fun _ hx => coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn
      i j hx)
    (fun _ hx => exists_eventually_contDiffOn_coordinate_source_transition U hU hD L he c hc
      hlower hopen hconn hsmooth i j hx) hbound m hx

include hD he hc hlower hopen hconn hsmooth in
theorem tendstoUniformlyOn_coordinate_source_transition_jet (i j : ι)
    (hbound : LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKU : K ⊆ Subtype.val '' overlap (fun i j => D i j) i j) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (coordinateRepresentative U hU
      (fun y => Function.invFun (e k j) (e k i y))))
      (iteratedFDeriv ℝ m
        (coordinateRepresentative U hU (transition (fun i j => D i j) i j))) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact (tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth
    (fun _ hx => coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn
      i j hx)
    (fun _ hx => exists_eventually_contDiffOn_coordinate_source_transition U hU hD L he c hc
      hlower hopen hconn hsmooth i j hx) hbound m).mono hKU

end PoincareConjecture.ChartDistance
