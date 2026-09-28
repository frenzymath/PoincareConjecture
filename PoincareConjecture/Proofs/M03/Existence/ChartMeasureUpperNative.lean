import PoincareConjecture.Proofs.M03.Existence.EuclideanJacobianBoundNative
import PoincareConjecture.Proofs.M03.Existence.NativeChartMeasureData
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.MeasureTheory.MeasurableSpace.Embedding









set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal Manifold ContDiff

universe u

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem measurableSet_chart_image (e : OpenPartialHomeomorph M E)
    {S : Set M} (hS : MeasurableSet S) (hSs : S ⊆ e.source) :
    MeasurableSet (e '' S) := by
  have hi : Measurable (fun y : e.target => e.symm (y : E)) :=
    (continuousOn_iff_continuous_domRestrict.mp e.symm.continuousOn).measurable
  have heq : e '' S =
      Subtype.val '' ((fun y : e.target => e.symm (y : E)) ⁻¹' S) := by
    rw [e.image_eq_target_inter_inv_preimage hSs]
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hy.1⟩, hy.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe e.open_target.measurableSet).measurableSet_image.mpr
    (hS.preimage hi)


def coordinatePushforward (e : OpenPartialHomeomorph M E) (K : Set M) : Measure M :=
  (volume.restrict (e '' K)).map e.symm

theorem coordinateInverse_aemeasurable (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source) :
    AEMeasurable e.symm (volume.restrict (e '' K)) :=
  (e.symm.continuousOn.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx))).aemeasurable (measurableSet_chart_image e hK hKs)

theorem coordinatePushforward_apply (e : OpenPartialHomeomorph M E)
    {K : Set M} (hK : MeasurableSet K) (hKs : K ⊆ e.source)
    {S : Set M} (hS : MeasurableSet S) :
    coordinatePushforward e K S = volume (e '' (S ∩ K)) := by
  rw [coordinatePushforward, Measure.map_apply_of_aemeasurable
    (coordinateInverse_aemeasurable e hK hKs) hS,
    Measure.restrict_apply' (measurableSet_chart_image e hK hKs)]
  congr 1
  ext y
  constructor
  · rintro ⟨hyS, x, hxK, rfl⟩
    change e.symm (e x) ∈ S at hyS
    rw [e.left_inv (hKs hxK)] at hyS
    exact ⟨x, ⟨hyS, hxK⟩, rfl⟩
  · rintro ⟨x, ⟨hxS, hxK⟩, rfl⟩
    refine ⟨?_, ⟨x, hxK, rfl⟩⟩
    change e.symm (e x) ∈ S
    rwa [e.left_inv (hKs hxK)]

variable [T2Space M]

theorem weightedChartMeasure_le_coordinatePushforward
    (e : OpenPartialHomeomorph M E) (φ : C(M, ℝ))
    (hcompact : IsCompact (tsupport φ)) (hsupport : tsupport φ ⊆ e.source)
    (hbound : ∀ x, φ x ≤ 1) :
    weightedChartMeasure e φ ≤ coordinatePushforward e (tsupport φ) :=
  Measure.map_mono_of_aemeasurable
    (weightedSourceMeasure_le e φ hcompact hsupport hbound)
    (coordinateInverse_aemeasurable e (isClosed_tsupport φ).measurableSet hsupport)

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def chartTransitionDomain (p q : M) : Set E :=
  (chartAt E p).target ∩ (chartAt E p).symm ⁻¹' (chartAt E q).source

theorem chartTransitionDomain_open (p q : M) : IsOpen (chartTransitionDomain (n := n) p q) :=
  (chartAt E p).isOpen_inter_preimage_symm (chartAt E q).open_source

theorem contDiffOn_chartTransition (p q : M) :
    ContDiffOn ℝ 1 ((chartAt E q) ∘ (chartAt E p).symm) (chartTransitionDomain p q) := by
  have he : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (chartAt E q) (chartAt E q).source :=
    contMDiffOn_chart (I := 𝓡 n) (x := q)
  have hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm (I := 𝓡 n) (x := p)
  exact (he.comp (hi.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn.of_le (by simp)


theorem exists_weightedChartMeasure_upper (p q : M) (φ : C(M, ℝ))
    (hcompact : IsCompact (tsupport φ))
    (hsupport : tsupport φ ⊆ (chartAt E q).source) (hbound : ∀ x, φ x ≤ 1)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : Set M, MeasurableSet S → S ⊆ K →
      weightedChartMeasure (chartAt E q) φ S ≤ ENNReal.ofReal B * volume (chartAt E p '' S) := by
  let e := chartAt E p
  let f := chartAt E q
  let C : Set E := e '' (K ∩ tsupport φ)
  have hC : IsCompact C :=
    (hK.inter_right (isClosed_tsupport φ)).image_of_continuousOn
      (e.continuousOn.mono (fun _ hx => hKs hx.1))
  have hCU : C ⊆ chartTransitionDomain p q := by
    rintro _ ⟨x, ⟨hxK, hxφ⟩, rfl⟩
    refine ⟨e.map_source (hKs hxK), ?_⟩
    change e.symm (e x) ∈ f.source
    rw [e.left_inv (hKs hxK)]
    exact hsupport hxφ
  obtain ⟨B, hB0, hB⟩ := EuclideanJacobianBoundNative.exists_volume_image_bound
    (chartTransitionDomain_open p q) (contDiffOn_chartTransition p q) hC hCU
  refine ⟨B, hB0, ?_⟩
  intro S hS hSK
  have hSL : MeasurableSet (S ∩ tsupport φ) := hS.inter (isClosed_tsupport φ).measurableSet
  have hSLsource : S ∩ tsupport φ ⊆ e.source := fun _ hx => hKs (hSK hx.1)
  have himage : MeasurableSet (e '' (S ∩ tsupport φ)) :=
    measurableSet_chart_image e hSL hSLsource
  have hsub : e '' (S ∩ tsupport φ) ⊆ C :=
    image_mono (fun _ hx => ⟨hSK hx.1, hx.2⟩)
  have htransition : (f ∘ e.symm) '' (e '' (S ∩ tsupport φ)) = f '' (S ∩ tsupport φ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change f (e.symm (e x)) ∈ f '' (S ∩ tsupport φ)
      rw [e.left_inv (hSLsource hx)]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
      change f (e.symm (e x)) = f x
      rw [e.left_inv (hSLsource hx)]
  calc
    weightedChartMeasure f φ S ≤ coordinatePushforward f (tsupport φ) S :=
      weightedChartMeasure_le_coordinatePushforward f φ hcompact hsupport hbound S
    _ = volume (f '' (S ∩ tsupport φ)) :=
      coordinatePushforward_apply f (isClosed_tsupport φ).measurableSet hsupport hS
    _ = volume ((f ∘ e.symm) '' (e '' (S ∩ tsupport φ))) := congrArg volume htransition.symm
    _ ≤ ENNReal.ofReal B * volume (e '' (S ∩ tsupport φ)) := hB _ himage hsub
    _ ≤ ENNReal.ofReal B * volume (e '' S) := by
      have hvol : volume (e '' (S ∩ tsupport φ)) ≤ volume (e '' S) :=
        measure_mono (image_mono inter_subset_left)
      exact mul_le_mul_right hvol (ENNReal.ofReal B)

namespace FiniteChartData

variable [CompactSpace M] (d : FiniteChartData (n := n) (M := M))


theorem exists_measure_restrict_le_chart (p : M) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      d.measure.restrict K ≤ C • coordinatePushforward (chartAt E p) K := by
  classical
  choose B hB0 hB using (fun i : d.centers =>
    exists_weightedChartMeasure_upper p i.val (d.weight i) (d.weight_compactSupport i)
      (d.weight_support_subset i) (d.weight_le_one i) hK hKs)
  let C : ℝ≥0∞ := ∑ i : d.centers, ENNReal.ofReal (B i)
  refine ⟨C, by simp [C], Measure.le_iff.mpr ?_⟩
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, smul_eq_mul,
    coordinatePushforward_apply (chartAt E p) hK.measurableSet hKs hS]
  change (Measure.sum (fun i : d.centers => weightedChartMeasure (d.chart i) (d.weight i)))
    (S ∩ K) ≤ _
  rw [Measure.sum_apply _ (hS.inter hK.measurableSet)]
  calc
    _ ≤ ∑' i : d.centers, ENNReal.ofReal (B i) * volume (chartAt E p '' (S ∩ K)) :=
      ENNReal.tsum_le_tsum (fun i => hB i (S ∩ K) (hS.inter hK.measurableSet) inter_subset_right)
    _ = _ := by rw [tsum_fintype, ← Finset.sum_mul]

end FiniteChartData

end PoincareConjecture.ChartMeasureNative
