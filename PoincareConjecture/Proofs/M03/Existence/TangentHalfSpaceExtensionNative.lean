import PoincareConjecture.Proofs.M03.Existence.HalfSpaceExtensionNative
import PoincareConjecture.Proofs.M03.Existence.SmoothManifoldLocalFlowNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Topology ContDiff Bundle BigOperators

noncomputable section

namespace PoincareConjecture.TangentHalfSpaceExtensionNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n
local notation "J" => ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 n)

def reflectionExtension {k : ℕ} (c : Fin (k + 1) → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) (t : ℝ) (x : M) : TangentSpace I x :=
  if 0 ≤ t then X t x else ∑ j, c j • X (HalfSpaceExtensionNative.reflectionScale k j * t) x

theorem reflectionExtension_of_nonneg {k : ℕ} (c : Fin (k + 1) → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) {t : ℝ} (ht : 0 ≤ t) (x : M) :
    reflectionExtension c X t x = X t x := by
  simp only [reflectionExtension, if_pos ht]

theorem reflectionExtension_of_negative {k : ℕ} (c : Fin (k + 1) → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) {t : ℝ} (ht : t < 0) (x : M) :
    reflectionExtension c X t x =
      ∑ j, c j • X (HalfSpaceExtensionNative.reflectionScale k j * t) x := by
  simp only [reflectionExtension, if_neg (not_le.mpr ht)]

def fiberCoordinates (X : ℝ → (x : M) → TangentSpace I x) (p : M) (q : ℝ × M) : E :=
  (trivializationAt E (TangentSpace I) p
    (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)).2

def chartCoordinates (X : ℝ → (x : M) → TangentSpace I x) (p : M) (q : ℝ × E) : E :=
  fiberCoordinates X p (q.1, (extChartAt I p).symm q.2)

theorem contDiffOn_chartCoordinates {k : ℕ∞}
    (X : ℝ → (x : M) → TangentSpace I x) {T : ℝ}
    (hX : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Ico 0 T ×ˢ univ)) (p : M) :
    ContDiffOn ℝ k (chartCoordinates X p) (Ico 0 T ×ˢ (extChartAt I p).target) := by
  let e := trivializationAt E (TangentSpace I) p
  have hXs := hX.mono (prod_mono subset_rfl (subset_univ (extChartAt I p).source))
  have hcoord : ContMDiffOn J 𝓘(ℝ, E) k (fiberCoordinates X p)
      (Ico 0 T ×ˢ (extChartAt I p).source) := by
    refine ((e.contMDiffOn_iff ?_).mp hXs).2
    intro q hq
    rw [e.mem_source]
    simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hq.2
  have hinv : ContMDiffOn 𝓘(ℝ, ℝ × E) J k
      (fun q : ℝ × E => (q.1, (extChartAt I p).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I p).target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_extChartAt_symm p).comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hq => hq.2))
  exact (hcoord.comp hinv (fun _ hq => ⟨hq.1, (extChartAt I p).map_target hq.2⟩)).contDiffOn

theorem chartCoordinates_reflection {k : ℕ} (c : Fin (k + 1) → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) (p : M) {q : ℝ × E}
    (hq : q.2 ∈ (extChartAt I p).target) :
    chartCoordinates (reflectionExtension c X) p q =
      HalfSpaceExtensionNative.reflectionExtension c (chartCoordinates X p) q := by
  classical
  let e := trivializationAt E (TangentSpace I) p
  have hbase : (extChartAt I p).symm q.2 ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I p).map_target hq
  by_cases ht : 0 ≤ q.1
  · rw [HalfSpaceExtensionNative.reflectionExtension_eqOn_upper c
      (chartCoordinates X p) ⟨ht, mem_univ _⟩]
    simp only [chartCoordinates, fiberCoordinates, reflectionExtension_of_nonneg c X ht]
  · rw [HalfSpaceExtensionNative.reflectionExtension_of_negative c
      (chartCoordinates X p) (lt_of_not_ge ht)]
    simp only [chartCoordinates, fiberCoordinates, reflectionExtension_of_negative c X
      (lt_of_not_ge ht), HalfSpaceExtensionNative.timeScale_apply,
      ← (trivializationAt E (TangentSpace I) p).continuousLinearMapAt_apply_of_mem
        (R := ℝ) hbase, map_sum, map_smul]

theorem fiberCoordinates_reflection {k : ℕ} (c : Fin (k + 1) → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x) (p : M) {q : ℝ × M}
    (hq : q.2 ∈ (extChartAt I p).source) :
    fiberCoordinates (reflectionExtension c X) p q =
      HalfSpaceExtensionNative.reflectionExtension c (chartCoordinates X p)
        (q.1, extChartAt I p q.2) := by
  rw [← chartCoordinates_reflection c X p ((extChartAt I p).map_source hq)]
  simp only [chartCoordinates, (extChartAt I p).left_inv hq]

theorem contMDiffOn_reflectionExtension (k : ℕ) (c : Fin (k + 1) → ℝ)
    (hc : ∀ m : Fin (k + 1),
      ∑ j, c j * HalfSpaceExtensionNative.reflectionScale k j ^ (m : ℕ) = 1)
    (X : ℝ → (x : M) → TangentSpace I x) {T : ℝ} (hT : 0 < T)
    (hX : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Ico 0 T ×ˢ univ)) :
    ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2 (reflectionExtension c X q.1 q.2) : TangentBundle I M))
      (Ioo (-T / ((k : ℝ) + 1)) T ×ˢ univ) := by
  intro q hq
  apply ContMDiffAt.contMDiffWithinAt
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_snd, ?_⟩
  have href := HalfSpaceExtensionNative.contDiffOn_reflectionExtension_slab_on k c hc
    (chartCoordinates X q.2) hT
    (show IsOpen (extChartAt I q.2).target by simpa using (chartAt E q.2).open_target)
    (contDiffOn_chartCoordinates X hX q.2)
  have hrefAt : ContDiffAt ℝ k
      (HalfSpaceExtensionNative.reflectionExtension c (chartCoordinates X q.2))
      (q.1, extChartAt I q.2 q.2) :=
    href.contDiffAt (prod_mem_nhds (isOpen_Ioo.mem_nhds hq.1)
      (extChartAt_target_mem_nhds q.2))
  have hchart : ContMDiffAt J 𝓘(ℝ, ℝ × E) k
      (fun z : ℝ × M => (z.1, extChartAt I q.2 z.2)) q := by
    apply (contMDiffAt_prod_module_iff _).mpr
    exact ⟨contMDiffAt_fst, contMDiffAt_extChartAt.comp q contMDiffAt_snd⟩
  have hcomp := hrefAt.contMDiffAt.comp q hchart
  apply hcomp.congr_of_eventuallyEq
  have hsource : ∀ᶠ z : ℝ × M in 𝓝 q, z.2 ∈ (extChartAt I q.2).source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (by simpa only [extChartAt_source] using
        (chartAt E q.2).open_source.mem_nhds (mem_chart_source E q.2))
  filter_upwards [hsource] with z hz
  exact fiberCoordinates_reflection c X q.2 hz

def extensionBump (k : ℕ) {T : ℝ} (hT : 0 < T) : ContDiffBump (T / 4) where
  rIn := T / 4
  rOut := T / 4 + T / (4 * ((k : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := lt_add_of_pos_right _ (by positivity)

theorem extensionBump_support_subset (k : ℕ) {T : ℝ} (hT : 0 < T) :
    tsupport (extensionBump k hT) ⊆ Ioo (-T / ((k : ℝ) + 1)) T := by
  intro t ht
  rw [(extensionBump k hT).tsupport_eq] at ht
  have hdist : |t - T / 4| ≤ T / 4 + T / (4 * ((k : ℝ) + 1)) := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, extensionBump] using ht
  have hdist' := abs_le.mp hdist
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hsmall : T / (4 * ((k : ℝ) + 1)) < T / ((k : ℝ) + 1) := by
    have hpos : 0 < T / ((k : ℝ) + 1) := div_pos hT hk
    have heq : T / (4 * ((k : ℝ) + 1)) = (T / ((k : ℝ) + 1)) / 4 := by
      field_simp [ne_of_gt hk]
    rw [heq]
    linarith
  have hupper : T / (4 * ((k : ℝ) + 1)) ≤ T / 4 := by
    apply div_le_div_of_nonneg_left hT.le (by norm_num)
    have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  constructor
  · rw [neg_div]
    linarith
  · linarith

theorem extensionBump_one (k : ℕ) {T : ℝ} (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Icc 0 (T / 2)) : extensionBump k hT t = 1 := by
  apply (extensionBump k hT).one_of_mem_closedBall
  change dist t (T / 4) ≤ T / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem exists_contMDiff_extension (k : ℕ)
    (X : ℝ → (x : M) → TangentSpace I x) {T : ℝ} (hT : 0 < T)
    (hX : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Ico 0 T ×ˢ univ)) :
    ∃ Y : ℝ → (x : M) → TangentSpace I x,
      ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
        (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M)) ∧
      ∀ t ∈ Icc 0 (T / 2), ∀ x, Y t x = X t x := by
  obtain ⟨c, hc⟩ := HalfSpaceExtensionNative.exists_reflectionWeights k
  let β := extensionBump k hT
  let Y := reflectionExtension c X
  let Z : ℝ → (x : M) → TangentSpace I x := fun t x => β t • Y t x
  have hY := contMDiffOn_reflectionExtension k c hc X hT hX
  have hglobal : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (Z q.1 q.2) : TangentBundle I M)) := by
    intro q
    by_cases hqβ : q.1 ∈ tsupport β
    · have htime := extensionBump_support_subset k hT hqβ
      have hYat : ContMDiffAt J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
          (fun z : ℝ × M => (Bundle.TotalSpace.mk' E z.2 (Y z.1 z.2) : TangentBundle I M)) q :=
        hY.contMDiffAt (prod_mem_nhds (isOpen_Ioo.mem_nhds htime) univ_mem)
      rw [Bundle.contMDiffAt_totalSpace] at hYat ⊢
      refine ⟨contMDiffAt_snd, ?_⟩
      let e := trivializationAt E (TangentSpace I) q.2
      have hscalar : ContMDiffAt J 𝓘(ℝ, ℝ) k (fun z : ℝ × M => β z.1) q :=
        β.contDiff.contMDiff.contMDiffAt.comp q contMDiffAt_fst
      have hmul := hscalar.smul hYat.2
      apply hmul.congr_of_eventuallyEq
      have hbase : ∀ᶠ z : ℝ × M in 𝓝 q, z.2 ∈ e.baseSet :=
        continuous_snd.continuousAt.preimage_mem_nhds
          (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) q.2))
      filter_upwards [hbase] with z hz
      change (e (Bundle.TotalSpace.mk' E z.2 (β z.1 • Y z.1 z.2) : TangentBundle I M)).2 =
        β z.1 • (e (Bundle.TotalSpace.mk' E z.2 (Y z.1 z.2) : TangentBundle I M)).2
      simp only [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hz, map_smul]
    · have hzero : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
          (fun z : ℝ × M => (Bundle.TotalSpace.mk' E z.2 0 : TangentBundle I M)) :=
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd
      apply hzero.contMDiffAt.congr_of_eventuallyEq
      have hβzero : ∀ᶠ t in 𝓝 q.1, β t = 0 := notMem_tsupport_iff_eventuallyEq.mp hqβ
      filter_upwards [continuous_fst.continuousAt.eventually hβzero] with z hz
      simp only [Z, hz, zero_smul]
  refine ⟨Z, hglobal, ?_⟩
  intro t ht x
  change β t • reflectionExtension c X t x = X t x
  rw [extensionBump_one k hT ht, one_smul, reflectionExtension_of_nonneg c X ht.1]

theorem exists_contMDiff_extension_swapped (k : ℕ)
    (X : ℝ → (x : M) → TangentSpace I x) {T : ℝ} (hT : 0 < T)
    (hX : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Ico 0 T ×ˢ univ)) :
    ∃ Y : (q : M × ℝ) → TangentSpace I q.1,
      ContMDiff (ModelWithCorners.prod I 𝓘(ℝ, ℝ)) (ModelWithCorners.prod I 𝓘(ℝ, E)) k
        (fun q : M × ℝ => (Bundle.TotalSpace.mk' E q.1 (Y q) : TangentBundle I M)) ∧
      ∀ t ∈ Icc 0 (T / 2), ∀ x, Y (x, t) = X t x := by
  obtain ⟨Y, hY, hEq⟩ := exists_contMDiff_extension k X hT hX
  exact ⟨fun q => Y q.2 q.1, hY.comp (contMDiff_snd.prodMk contMDiff_fst), hEq⟩

end PoincareConjecture.TangentHalfSpaceExtensionNative

end
