import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.CompactImage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberEquiv
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import Mathlib.MeasureTheory.Integral.Bochner.Set









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
namespace PoincareConjecture.RiemannianMetric


private theorem volumeMeasure_image_le_of_tangentNorm_le_on_compact_superset
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : PoincareConjecture.RiemannianMetric n M) (h : PoincareConjecture.RiemannianMetric n N)
    {f : M → N} {U s t : Set M} (hU : IsOpen U)
    (hs : MeasurableSet s) (ht : IsCompact t) (hst : s ⊆ t) (htU : t ⊆ U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 f U)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ C * g.tangentNorm x v) :
    h.volumeMeasure (f '' s) ≤ ENNReal.ofReal C ^ n * g.volumeMeasure s := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | hne
  · have hs0 : s = ∅ := subset_empty_iff.mp hst
    simp [hs0]
  let : Nonempty t := hne.to_subtype
  have hlocal (p : t) : ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y :=
    g.exists_open_edist_image_le_of_tangentNorm_le h (hU.mem_nhds (htU p.2))
      (fun z hz => hf.contMDiffAt (hU.mem_nhds hz)) hC hbound
  choose V hVo hpV hVU hdist using hlocal
  obtain ⟨a, ha⟩ := ht.isLindelof.indexed_countable_subcover V hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, hpV ⟨x,hx⟩⟩)
  let W : ℕ → Set M := fun i => V (a i) ∩ s
  have hWm (i : ℕ) : MeasurableSet (W i) := (hVo _).measurableSet.inter hs
  have hcover : (⋃ i, W i) = s := by
    apply Subset.antisymm (iUnion_subset fun i => inter_subset_right)
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ha (hst hx))
    exact mem_iUnion.mpr ⟨i, hi, hx⟩
  have hDm (i : ℕ) : MeasurableSet (disjointed W i) := MeasurableSet.disjointed hWm i
  have hD (i : ℕ) : h.volumeMeasure (f '' disjointed W i) ≤
      ENNReal.ofReal C ^ n * g.volumeMeasure (disjointed W i) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
    let K : ℝ≥0 := ⟨C,hC.le⟩
    have hK : (K : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq K
    have hLip : LipschitzOnWith K f (disjointed W i) := by
      intro x hx y hy
      change h.edist (f x) (f y) ≤ (K : ℝ≥0∞) * g.edist x y
      rw [hK]
      exact hdist (a i) x ((disjointed_le W i hx).1)
        y ((disjointed_le W i hy).1)
    change Measure.euclideanHausdorffMeasure n (f '' disjointed W i) ≤
      ENNReal.ofReal C ^ n * Measure.euclideanHausdorffMeasure n (disjointed W i)
    simpa only [hK] using
      Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le hLip n
  have hpartition : (⋃ i, disjointed W i) = s := (iUnion_disjointed).trans hcover
  calc
    h.volumeMeasure (f '' s) = h.volumeMeasure (⋃ i, f '' disjointed W i) := by
      rw [← image_iUnion, hpartition]
    _ ≤ ∑' i, h.volumeMeasure (f '' disjointed W i) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal C ^ n * g.volumeMeasure (disjointed W i) :=
      ENNReal.tsum_le_tsum hD
    _ = ENNReal.ofReal C ^ n * g.volumeMeasure s := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion (disjoint_disjointed W) hDm, hpartition]


private theorem measurePreserving_restrict_of_openPartialHomeomorph_norm_eq
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) (he : MeasurableEmbedding e)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hnorm : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) = g.tangentNorm x v)
    (hinorm : ∀ y ∈ e.target, ∀ v : TangentSpace (𝓡 n) y,
      g.tangentNorm (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) = h.tangentNorm y v)
    {s : Set M} (hs : IsCompact s) (hse : s ⊆ e.source) :
    MeasurePreserving e (g.volumeMeasure.restrict s)
      (h.volumeMeasure.restrict (e '' s)) := by
  have hes : IsCompact (e '' s) := hs.image_of_continuousOn (e.continuousOn.mono hse)
  have himage {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ s) :
      h.volumeMeasure (e '' A) = g.volumeMeasure A := by
    have hAe : A ⊆ e.source := hAs.trans hse
    have hforward := volumeMeasure_image_le_of_tangentNorm_le_on_compact_superset
      g h e.open_source hA hs hAs hse hf (show (0 : ℝ) < 1 by norm_num)
      (fun x hx v => by simpa only [one_mul] using (hnorm x hx v).le)
    have hbackward := volumeMeasure_image_le_of_tangentNorm_le_on_compact_superset
      h g e.open_target (he.measurableSet_image' hA) hes
      (image_mono hAs) (image_subset_iff.mpr (fun x hx => e.map_source (hse hx)))
      hi (show (0 : ℝ) < 1 by norm_num)
      (fun y hy v => by simpa only [one_mul] using (hinorm y hy v).le)
    have hset : e.symm '' (e '' A) = A := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa only [e.left_inv (hAe hz)] using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.left_inv (hAe hx)⟩
    rw [hset] at hbackward
    simp only [ENNReal.ofReal_one, one_pow, one_mul] at hforward hbackward
    exact le_antisymm hforward hbackward
  refine ⟨he.measurable, ?_⟩
  ext B hB
  rw [Measure.map_apply he.measurable hB, Measure.restrict_apply (hB.preimage he.measurable),
    Measure.restrict_apply hB]
  rw [← himage ((hB.preimage he.measurable).inter hs.measurableSet) inter_subset_right]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxB, hxs⟩, rfl⟩
    exact ⟨hxB, ⟨x, hxs, rfl⟩⟩
  · rintro ⟨hyB, x, hxs, rfl⟩
    exact ⟨x, ⟨hyB, hxs⟩, rfl⟩

private theorem tangentNorm_symm_of_openPartialHomeomorph_metric
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hmetric : ∀ x ∈ e.source, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (y : N) (hy : y ∈ e.target) (v : TangentSpace (𝓡 n) y) :
    g.tangentNorm (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) =
      h.tangentNorm y v := by
  have heq : (e ∘ e.symm) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hcomp := mfderiv_comp y
    (((hf _ (e.map_target hy)).contMDiffAt
      (e.open_source.mem_nhds (e.map_target hy))).mdifferentiableAt (by simp))
    (((hi y hy).contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp))
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  have hv : mfderiv (𝓡 n) (𝓡 n) e (e.symm y)
      (mfderiv (𝓡 n) (𝓡 n) e.symm y v) = v := by
    exact (congrArg (fun A => A v) hcomp).symm
  unfold tangentNorm
  rw [hmetric _ (e.map_target hy), hv, e.right_inv hy]



theorem openRegularFiberMetric_restriction_transport
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    (g : RiemannianMetric (m+k) M) {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U V : Opens M) (hVU : (V : Set M) ⊆ U)
    (hreg : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) f x)) (c : Fin k → ℝ) :
    let hregV := fun x hx => hreg x (hVU hx)
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    letI := openFiberChartedSpace (m := m) hf V hregV c
    letI := isManifold_openFiber (m := m) hf V hregV c
    let gU := g.openRegularFiberMetric hf U hreg c
    let gV := g.openRegularFiberMetric hf V hregV c
    let j : openFiber f V c → openFiber f U c := fun x =>
      ⟨⟨openFiberIncl f V c x, hVU x.1.2⟩, x.2⟩
    ContMDiff (𝓡 m) (𝓡 m) ∞ j ∧ Topology.IsOpenEmbedding j ∧
      (∀ (x : openFiber f V c) (v w : TangentSpace (𝓡 m) x),
        gV.inner x v w = gU.inner (j x)
          (mfderiv (𝓡 m) (𝓡 m) j x v) (mfderiv (𝓡 m) (𝓡 m) j x w)) ∧
      (∀ x, gV.leviCivitaData.scalarCurvature x =
        gU.leviCivitaData.scalarCurvature (j x)) ∧
      ∀ s : Set (openFiber f V c), IsCompact s →
        MeasurePreserving j (gV.volumeMeasure.restrict s)
          (gU.volumeMeasure.restrict (j '' s)) ∧
        (∀ F : openFiber f U c → ℝ,
          (∫ x in s, F (j x) ∂gV.volumeMeasure) =
            ∫ y in j '' s, F y ∂gU.volumeMeasure) ∧
        ∀ Ψ : ℝ → ℝ,
          (∫ x in s, Ψ (gV.leviCivitaData.scalarCurvature x) ∂gV.volumeMeasure) =
            ∫ y in j '' s, Ψ (gU.leviCivitaData.scalarCurvature y) ∂gU.volumeMeasure := by
  classical
  dsimp only
  let hregV := fun x hx => hreg x (hVU hx)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let := openFiberChartedSpace (m := m) hf V hregV c
  let := isManifold_openFiber (m := m) hf V hregV c
  let gU := g.openRegularFiberMetric hf U hreg c
  let gV := g.openRegularFiberMetric hf V hregV c
  let j : openFiber f V c → openFiber f U c := fun x =>
    ⟨⟨openFiberIncl f V c x, hVU x.1.2⟩, x.2⟩
  have hj : ContMDiff (𝓡 m) (𝓡 m) ∞ j := by
    intro x
    apply (contMDiffAt_into_openFiber_iff (m := m) hf c U hreg j x).mpr
    exact contMDiff_openFiberIncl (m := m) hf V hregV c x
  have hrange : Set.range j = openFiberIncl f U c ⁻¹' (V : Set M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.1.2
    · intro hx
      exact ⟨⟨⟨openFiberIncl f U c x, hx⟩, x.2⟩, rfl⟩
  have hemb : Topology.IsOpenEmbedding j := by
    refine ⟨(isEmbedding_openFiberIncl f U c).of_comp_iff.mp
      (isEmbedding_openFiberIncl f V c), ?_⟩
    rw [hrange]
    exact V.isOpen.preimage (contMDiff_openFiberIncl (m := m) hf U hreg c).continuous
  have hmetric (x : openFiber f V c) (v w : TangentSpace (𝓡 m) x) :
      gV.inner x v w = gU.inner (j x)
        (mfderiv (𝓡 m) (𝓡 m) j x v) (mfderiv (𝓡 m) (𝓡 m) j x w) := by
    have hcomp := mfderiv_comp x
      ((contMDiff_openFiberIncl (m := m) hf U hreg c (j x)).mdifferentiableAt (by simp))
      (hj.mdifferentiable (by simp) x)
    have heq : openFiberIncl f U c ∘ j = openFiberIncl f V c := rfl
    rw [heq] at hcomp
    change (g.openRegularFiberMetric hf V hregV c).inner x v w =
      (g.openRegularFiberMetric hf U hreg c).inner (j x)
        (mfderiv (𝓡 m) (𝓡 m) j x v) (mfderiv (𝓡 m) (𝓡 m) j x w)
    simp only [openRegularFiberMetric_inner]
    rw [hcomp]
    rfl
  have hscalar (x : openFiber f V c) :
      gV.leviCivitaData.scalarCurvature x = gU.leviCivitaData.scalarCurvature (j x) :=
    gV.leviCivitaData.scalarCurvature_eq_of_local_isometry
      gU.leviCivitaData isOpen_univ hj.contMDiffOn (fun x _ => hmetric x) (mem_univ x)
  refine ⟨hj, hemb, hmetric, hscalar, ?_⟩
  intro s hs
  have hmeasure : MeasurePreserving j (gV.volumeMeasure.restrict s)
      (gU.volumeMeasure.restrict (j '' s)) := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨hemb.measurableEmbedding.measurable, by simp⟩
    let : Nonempty (openFiber f V c) := ⟨hne.some⟩
    let e := hemb.toOpenPartialHomeomorph j
    have hefunc : (e : openFiber f V c → openFiber f U c) = j := by simp [e]
    have hesource : e.source = univ := by simp [e]
    have hesmooth : ContMDiffOn (𝓡 m) (𝓡 m) 1 e e.source := by
      simpa only [hefunc] using (hj.of_le (by simp)).contMDiffOn
    have hismooth : ContMDiffOn (𝓡 m) (𝓡 m) 1 e.symm e.target := by
      intro x hx
      have hlocal : ContMDiffAt (𝓡 m) (𝓡 m) ∞ e.symm x := by
        apply (contMDiffAt_into_openFiber_iff (m := m) hf c V hregV e.symm x).mpr
        apply (contMDiff_openFiberIncl (m := m) hf U hreg c x).congr_of_eventuallyEq
        filter_upwards [e.open_target.mem_nhds hx] with y hy
        exact congrArg (openFiberIncl f U c) (e.right_inv hy)
      exact (hlocal.of_le (by simp)).contMDiffWithinAt
    have hemetric : ∀ x ∈ e.source, ∀ v w : TangentSpace (𝓡 m) x,
        gV.inner x v w = gU.inner (e x)
          (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w) := by
      intro x hx v w
      change gV.inner x v w = gU.inner (j x)
        (mfderiv (𝓡 m) (𝓡 m) j x v) (mfderiv (𝓡 m) (𝓡 m) j x w)
      exact hmetric x v w
    have hme := measurePreserving_restrict_of_openPartialHomeomorph_norm_eq
      gV gU e (by simpa only [hefunc] using hemb.measurableEmbedding)
      hesmooth hismooth
      (fun x hx v => congrArg Real.sqrt (hemetric x hx v v).symm)
      (tangentNorm_symm_of_openPartialHomeomorph_metric gV gU e hesmooth hismooth hemetric)
      hs (by rw [hesource]; exact subset_univ _)
    simpa only [hefunc] using hme
  refine ⟨hmeasure, fun F => hmeasure.integral_comp hemb.measurableEmbedding F, ?_⟩
  intro Ψ
  calc
    _ = ∫ x in s, Ψ (gU.leviCivitaData.scalarCurvature (j x)) ∂gV.volumeMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => congrArg Ψ (hscalar x)
    _ = _ := hmeasure.integral_comp hemb.measurableEmbedding
      (fun x => Ψ (gU.leviCivitaData.scalarCurvature x))

end PoincareConjecture.RiemannianMetric
