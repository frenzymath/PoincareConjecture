import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicDistanceVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic
import Mathlib.Topology.Compactness.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

universe u

namespace PoincareConjecture.M28

open EndpointVariation CoordinateExponential

private theorem contDiffOn_one_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q w : ℝ → E} {S : Set ℝ} (hS : IsOpen S)
    (hq : ∀ t ∈ S, HasDerivAt q (w t) t) (hw : ContinuousOn w S) :
    ContDiffOn ℝ 1 q S := by
  apply (contDiffOn_one_iff_derivWithin hS.uniqueDiffOn).mpr
  refine ⟨fun t ht => (hq t ht).differentiableAt.differentiableWithinAt, ?_⟩
  apply hw.congr
  intro t ht
  exact (hq t ht).hasDerivWithinAt.derivWithin (hS.uniqueDiffOn t ht)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_terminal_chart_variation
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {η σ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hη : g.IsGeodesicOn η (Icc 0 L))
    (hηU : MapsTo η (Icc 0 L) (U : Set M))
    (hσ0 : σ 0 = η L) (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 1 σ 0) :
    let c := extChartAt (𝓡 3) (η L)
    let q := fun t => c (η t)
    let v := fun s => c (σ s) - q L
    ∃ a r : ℝ, 0 < a ∧ a < L ∧ 0 < r ∧
      ContDiffOn ℝ 1 q (Ioo (a - r) (L + r)) ∧
      ContDiffOn ℝ 1 (deriv q) (Ioo (a - r) (L + r)) ∧
      ContDiffOn ℝ 1 v (Ioo (-r) r) ∧
      MapsTo η (Ioo (a - r) (L + r)) c.source ∧
      MapsTo σ (Ioo (-r) r) c.source ∧
      MapsTo (position q v a L)
        (Ioo (-r) r ×ˢ Ioo (a - r) (L + r)) (c.target ∩ c.symm ⁻¹' (U : Set M)) ∧
      ∀ t ∈ Ioo (a - r) (L + r),
        HasDerivAt q (deriv q t) t ∧
        HasDerivAt (deriv q)
          (-coordinateChristoffel (g.pullbackCoefficients c.symm)
            (q t) (deriv q t) (deriv q t)) t := by
  let c := extChartAt (𝓡 3) (η L)
  let q := fun t => c (η t)
  let v := fun s => c (σ s) - q L
  change ∃ a r : ℝ, _
  have hLmem : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  obtain ⟨V, hVopen, hLV, hηV⟩ := hη.exists_open_nhds hLmem
  have hp : η L ∈ c.source := mem_extChartAt_source (I := 𝓡 3) (η L)
  have hηlocal : η ⁻¹' ((U : Set M) ∩ c.source) ∈ 𝓝 L :=
    (hη.contMDiffAt hLmem).continuousAt.preimage_mem_nhds
      ((U.isOpen.inter (isOpen_extChartAt_source (I := 𝓡 3) (η L))).mem_nhds
        ⟨hηU hLmem, hp⟩)
  obtain ⟨l, b, hlb, hinterval⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem (hVopen.mem_nhds hLV) hηlocal)
  let δ := min (L - l) (min (b - L) L) / 4
  have hδ : 0 < δ := by
    apply div_pos _ (by norm_num)
    exact lt_min (sub_pos.mpr hlb.1) (lt_min (sub_pos.mpr hlb.2) hL)
  have hδl : δ ≤ (L - l) / 4 := div_le_div_of_nonneg_right
    (min_le_left _ _) (by norm_num)
  have hδb : δ ≤ (b - L) / 4 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hδL : δ ≤ L / 4 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  let J := Ioo (L - 2 * δ) (L + 2 * δ)
  have hJsub : J ⊆ Ioo l b := by
    intro t ht
    change L - 2 * δ < t ∧ t < L + 2 * δ at ht
    constructor <;> linarith [ht.1, ht.2]
  have hηchart : MapsTo η J c.source :=
    fun t ht => (hinterval (hJsub ht)).2.2
  have hηregion : MapsTo η J (U : Set M) :=
    fun t ht => (hinterval (hJsub ht)).2.1
  have hgeod : g.IsGeodesicOn η J :=
    fun t ht => hηV t (hinterval (hJsub ht)).1
  have hODE := hgeod.hasDerivAt_in_chart isOpen_Ioo (η L) hηchart
  have hqC1 : ContDiffOn ℝ 1 q J := by
    apply contDiffOn_one_of_hasDerivAt isOpen_Ioo (fun t ht => (hODE t ht).1)
    exact fun t ht => (hODE t ht).2.continuousAt.continuousWithinAt
  have hwC1 : ContDiffOn ℝ 1 (deriv q) J := by
    apply contDiffOn_one_of_hasDerivAt isOpen_Ioo (fun t ht => (hODE t ht).2)
    intro t ht
    have hqt : q t ∈ c.target := c.map_source (hηchart ht)
    have hB := (g.contDiffOn_chartCoefficients (η L)).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) (η L)).mem_nhds hqt)
    have hΓ := (contDiffAt_christoffelBilinear hB
      (g.isInvertible_chartCoefficients (η L) hqt)).continuousAt
    have hqc := (hODE t ht).1.continuousAt
    have hwc := (hODE t ht).2.continuousAt
    exact (((hΓ.comp hqc).clm_apply hwc).clm_apply hwc).neg.continuousWithinAt
  have hσsource : σ 0 ∈ c.source := by simpa only [hσ0] using hp
  have hvC1 : ContDiffAt ℝ 1 v 0 := by
    have hcσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 1 (c ∘ σ) 0 :=
      (contMDiffAt_extChartAt' (I := 𝓡 3) (n := 1)
        (by simpa only [c, extChartAt_source] using hσsource)).comp 0 hσ
    exact hcσ.contDiffAt.sub contDiffAt_const
  have hσsourceLocal : σ ⁻¹' c.source ∈ 𝓝 0 :=
    hσ.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 3) (η L)).mem_nhds hσsource)
  obtain ⟨lσ, bσ, hlσbσ, hσinterval⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hvC1.eventually (by norm_num)).and hσsourceLocal)
  let I := Ioo lσ bσ
  have h0I : (0 : ℝ) ∈ I := hlσbσ
  have hvI : ContDiffOn ℝ 1 v I :=
    fun s hs => (hσinterval hs).1.contDiffWithinAt
  have hσI : MapsTo σ I c.source := fun s hs => (hσinterval hs).2
  let a := L - δ
  have ha : 0 < a := by dsimp only [a]; linarith
  have haL : a < L := by dsimp only [a]; linarith
  let K := Icc (a - δ / 2) (L + δ / 2)
  have hKJ : K ⊆ J := by
    intro t ht
    change a - δ / 2 ≤ t ∧ t ≤ L + δ / 2 at ht
    change L - 2 * δ < t ∧ t < L + 2 * δ
    dsimp only [a] at ht
    constructor <;> linarith [ht.1, ht.2]
  let Ω := c.target ∩ c.symm ⁻¹' (U : Set M)
  have hΩ : IsOpen Ω :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := 1) (η L)).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓡 3) (η L)) U.isOpen
  let W := (I ×ˢ J) ∩ (position q v a L) ⁻¹' Ω
  have hW : IsOpen W :=
    (contDiffOn_position hqC1 hvI).continuousOn.isOpen_inter_preimage
      (isOpen_Ioo.prod isOpen_Ioo) hΩ
  have hv0 : v 0 = 0 := by simp only [v, q, hσ0, sub_self]
  have hbase : ({0} : Set ℝ) ×ˢ K ⊆ W := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hs0 : s = 0 := mem_singleton_iff.mp hs
    subst s
    refine ⟨⟨h0I, hKJ ht⟩, ?_⟩
    change position q v a L (0, t) ∈ Ω
    simp only [position, hv0, smul_zero, add_zero]
    refine ⟨c.map_source (hηchart (hKJ ht)), ?_⟩
    change c.symm (c (η t)) ∈ U
    rw [c.left_inv (hηchart (hKJ ht))]
    exact hηregion (hKJ ht)
  obtain ⟨I', J', hI'open, _, h0I', hKJ', hprod⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hW hbase
  obtain ⟨l', b', hl'b', hI'sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hI'open.mem_nhds (h0I' (show (0 : ℝ) ∈ ({0} : Set ℝ) by simp)))
  let r := min (-l') (min b' (δ / 2)) / 2
  have hr : 0 < r := by
    apply div_pos _ (by norm_num)
    exact lt_min (by linarith [hl'b'.1])
      (lt_min hl'b'.2 (by positivity))
  have hrl : r ≤ -l' / 2 := div_le_div_of_nonneg_right
    (min_le_left _ _) (by norm_num)
  have hrb : r ≤ b' / 2 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hrδ : r ≤ δ / 4 := by
    have h := div_le_div_of_nonneg_right
      ((min_le_right (-l') (min b' (δ / 2))).trans (min_le_right b' (δ / 2)))
      (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp only [r]
    linarith
  have hIfinal : Ioo (-r) r ⊆ I' := by
    intro s hs
    apply hI'sub
    constructor <;> linarith [hs.1, hs.2, hl'b'.1, hl'b'.2]
  have hJfinal : Ioo (a - r) (L + r) ⊆ K := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hfinal : MapsTo (position q v a L)
      (Ioo (-r) r ×ˢ Ioo (a - r) (L + r)) Ω :=
    fun _ h => (hprod ⟨hIfinal h.1, hKJ' (hJfinal h.2)⟩).2
  have hIsub : Ioo (-r) r ⊆ I := by
    intro s hs
    have hLK : L ∈ K := by
      change a - δ / 2 ≤ L ∧ L ≤ L + δ / 2
      constructor <;> linarith
    exact (@hprod (s, L) ⟨hIfinal hs, @hKJ' L hLK⟩).1.1
  refine ⟨a, r, ha, haL, hr, hqC1.mono (hJfinal.trans hKJ),
    hwC1.mono (hJfinal.trans hKJ), hvI.mono hIsub,
    fun _ h => hηchart (hKJ (hJfinal h)),
    fun _ h => hσI (hIsub h), hfinal, ?_⟩
  exact fun t ht => hODE t (hKJ (hJfinal ht))

end PoincareConjecture.M28
