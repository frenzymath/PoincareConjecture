import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeNormalization
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCapBoundaryContact
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M13.OrdinaryFlow











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

private theorem intrinsicEDist_scaleSmoothMetric
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (Q : ℝ) (hQ : 0 < Q)
    {U : Set M} {p q : M} :
    intrinsicEDist (M13.scaleSmoothMetric g Q hQ) U p q =
      ENNReal.ofReal (Real.sqrt Q) * intrinsicEDist g U p q := by
  let h : RiemannianMetric 3 M := M13.scaleSmoothMetric g Q hQ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt Q)
  have hc0 : c ≠ 0 := ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ) |>.ne'
  have hct : c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  change intrinsicEDist (M13.scaleSmoothMetric g Q hQ) U p q =
    c * intrinsicEDist g U p q
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hdist : intrinsicEDist g U p q < r / c :=
      (ENNReal.lt_div_iff_mul_lt (.inl hc0) (.inl hct)).mpr (by
        simpa [mul_comm] using hr)
    obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγlen⟩ :=
      exists_intrinsic_competitor g hdist
    have hscale := M13.homothety_pathELength g h
      (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
      (M13.identity_metricHomothety g Q hQ) γ 0 1 hγ
    change h.pathELength γ 0 1 =
      c * g.pathELength γ 0 1 at hscale
    have hle := intrinsicEDist_le_pathELength
      h zero_le_one hγ hγU
    rw [hγ0, hγ1] at hle
    exact (calc
      intrinsicEDist h U p q ≤ h.pathELength γ 0 1 := hle
      _ = c * g.pathELength γ 0 1 := hscale
      _ < r := ENNReal.mul_lt_of_lt_div' hγlen).le
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγlen⟩ :=
      exists_intrinsic_competitor h hr
    have hscale := M13.homothety_pathELength g h
      (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
      (M13.identity_metricHomothety g Q hQ) γ 0 1 hγ
    change h.pathELength γ 0 1 =
      c * g.pathELength γ 0 1 at hscale
    have hle := intrinsicEDist_le_pathELength g zero_le_one hγ hγU
    rw [hγ0, hγ1] at hle
    exact (calc
      c * intrinsicEDist g U p q ≤ c * g.pathELength γ 0 1 :=
        by simpa only [mul_comm] using (mul_le_mul_left hle c)
      _ = h.pathELength γ 0 1 := hscale.symm
      _ < r := hγlen).le




theorem normalizedSlice_intrinsicEDist (H : CounterexampleNeckFamily E) (k : ℕ)
    (U : Set ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier)
    (p q : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) :
    intrinsicEDist (H.normalizedSliceMetric k) U p q =
      ENNReal.ofReal (Real.sqrt ((E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩)) *
        intrinsicEDist ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
          U p q :=
  intrinsicEDist_scaleSmoothMetric _ _ (H.base_scalar_pos k)




theorem normalizedSlice_source_path_minimizing
    (H : CounterexampleNeckFamily E) (k : ℕ) :
    (H.normalizedSliceMetric k).pathELength (H.segment k).path 0 1 ≠ ⊤ ∧
      (H.normalizedSliceMetric k).pathELength (H.segment k).path 0 1 =
        intrinsicEDist (H.normalizedSliceMetric k)
          (H.segment k).source_region.carrier
          ((H.segment k).path 0) ((H.segment k).path 1) := by
  let S := H.segment k
  let g := (E (k + H.shift)).flow.metric (E (k + H.shift)).time
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hnorm := M13.homothety_pathELength g (H.normalizedSliceMetric k)
    (Diffeomorph.refl (𝓡 3) _ ∞) Q (H.base_scalar_pos k)
    (M13.identity_metricHomothety g Q (H.base_scalar_pos k)) S.path 0 1
    S.path_smooth
  change (H.normalizedSliceMetric k).pathELength S.path 0 1 =
    ENNReal.ofReal (Real.sqrt Q) * g.pathELength S.path 0 1 at hnorm
  constructor
  · rw [hnorm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top S.source_region.finite_length
  · rw [hnorm, H.normalizedSlice_intrinsicEDist]
    rw [S.source_region.minimizing]

private theorem retained_tube_subset_source_region
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k))
    {epsilon₀ : ℝ}
    (hregion : ∀ {epsilon C A D₀ D : ℝ}
      {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
      (S : CounterexampleNeckSegment E),
      0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
      CounterexampleNeckSegment.neckCarrierUnion S ⊆ S.source_region.carrier)
    (hsmall : epsilon ≤ epsilon₀) (k : ℕ) :
    (T k).carrierOpen.1 ⊆ (H.segment k).source_region.carrier := by
  exact (T k).carrier_subset_neckCarrierUnion.trans
    (hregion (H.segment k) (H.base_scalar_pos k) hsmall)

theorem exists_retained_path_minimizing_in_tube_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ →
        ∀ k (a b : ℝ), a ∈ Icc (H.segment k).lower (H.segment k).upper →
          b ∈ Icc (H.segment k).lower (H.segment k).upper → a ≤ b →
          (H.normalizedSliceMetric k).pathELength (H.segment k).path a b =
            intrinsicEDist (H.normalizedSliceMetric k) (T k).tube.carrier
              ((H.segment k).path a) ((H.segment k).path b) := by
  obtain ⟨epsilon₀, hpos, hsmall, hregion⟩ :=
    exists_source_neck_region_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hbound k a b ha hb hab
  let S := H.segment k
  let g := (E (k + H.shift)).flow.metric (E (k + H.shift)).time
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let g' := H.normalizedSliceMetric k
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 S.path (Icc a b) := by
    exact S.path_smooth.mono (Icc_subset_Icc
      (S.lower_pos.le.trans ha.1) (hb.2.trans S.upper_lt_one.le))
  have hpathU : MapsTo S.path (Icc a b) S.source_region.carrier := by
    exact S.source_region.path_mem.mono (Icc_subset_Icc
      (S.lower_pos.le.trans ha.1) (hb.2.trans S.upper_lt_one.le)) (Subset.refl _)
  have hfinite : g'.pathELength S.path 0 1 ≠ ⊤ := by
    have hwhole : g.pathELength S.path 0 1 ≠ ⊤ := S.source_region.finite_length
    have hnorm := M13.homothety_pathELength g g'
      (Diffeomorph.refl (𝓡 3) _ ∞) Q (H.base_scalar_pos k)
      (M13.identity_metricHomothety g Q (H.base_scalar_pos k)) S.path 0 1
      S.path_smooth
    have hnorm' : g'.pathELength S.path 0 1 =
        ENNReal.ofReal (Real.sqrt Q) * g.pathELength S.path 0 1 := by
      change g'.pathELength S.path 0 1 =
        ENNReal.ofReal (Real.sqrt Q) * g.pathELength S.path 0 1 at hnorm
      exact hnorm
    have hwhole' : g'.pathELength S.path 0 1 ≠ ⊤ := by
      rw [hnorm']
      exact ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) hwhole
    exact hwhole'
  have hminSource : g'.pathELength S.path a b =
      intrinsicEDist g' S.source_region.carrier (S.path a) (S.path b) := by
    have hwhole : g'.pathELength S.path 0 1 =
        intrinsicEDist g' S.source_region.carrier (S.path 0) (S.path 1) := by
      have hnorm := M13.homothety_pathELength g g'
        (Diffeomorph.refl (𝓡 3) _ ∞) Q (H.base_scalar_pos k)
        (M13.identity_metricHomothety g Q (H.base_scalar_pos k)) S.path 0 1
        S.path_smooth
      change g'.pathELength S.path 0 1 =
        ENNReal.ofReal (Real.sqrt Q) * g.pathELength S.path 0 1 at hnorm
      have hscale := intrinsicEDist_scaleSmoothMetric g Q
        (H.base_scalar_pos k) (U := S.source_region.carrier)
        (p := S.path 0) (q := S.path 1)
      have hscale' : intrinsicEDist g' S.source_region.carrier (S.path 0) (S.path 1) =
          ENNReal.ofReal (Real.sqrt Q) *
            intrinsicEDist g S.source_region.carrier (S.path 0) (S.path 1) := by
        simpa [g', normalizedSliceMetric, g, Q] using
          (intrinsicEDist_scaleSmoothMetric g Q (H.base_scalar_pos k))
      rw [hnorm, hscale', S.source_region.minimizing]
    exact pathELength_eq_intrinsicEDist_subsegment g'
      (S.lower_pos.le.trans ha.1) hab (hb.2.trans S.upper_lt_one.le)
      S.path_smooth S.source_region.path_mem hfinite hwhole
  have hsubset : (T k).tube.carrier ⊆ S.source_region.carrier := by
    intro x hx
    exact retained_tube_subset_source_region H T
      (fun {epsilon C A D₀ D} {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
          S hQ hs => (hregion E S hQ hs).2.1) hbound k hx
  have hpathT : MapsTo S.path (Icc a b) (T k).tube.carrier := by
    intro t ht
    exact (T k).path_mem
      (Icc_subset_Icc ha.1 hb.2 ht)
  have hupper : intrinsicEDist g' (T k).tube.carrier (S.path a) (S.path b) ≤
      g'.pathELength S.path a b := by
    exact intrinsicEDist_le_pathELength g' hab hpath hpathT
  have hmono := intrinsicEDist_mono_of_subset (g := g') hsubset
    (p := S.path a) (q := S.path b)
  exact le_antisymm (hminSource ▸ hmono) hupper

theorem retained_path_base_distance_eq_length
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k))
    (hmin :
      ∀ k (a b : ℝ), a ∈ Icc (H.segment k).lower (H.segment k).upper →
        b ∈ Icc (H.segment k).lower (H.segment k).upper → a ≤ b →
        (H.normalizedSliceMetric k).pathELength (H.segment k).path a b =
          intrinsicEDist (H.normalizedSliceMetric k) (T k).tube.carrier
            ((H.segment k).path a) ((H.segment k).path b))
    (k : ℕ) (b : ℝ) (hb : b ∈ Icc (H.segment k).lower (H.segment k).upper) :
    (H.tubeMetric T k).edist (H.tubeBase T k)
        ⟨(H.segment k).path b, (T k).path_mem hb⟩ =
      ENNReal.ofReal ((H.normalizedSliceMetric k).pathELength
        (H.segment k).path (H.segment k).lower b).toReal := by
  rw [tubeMetric, intrinsicOpenMetric_edist]
  change intrinsicEDist (H.normalizedSliceMetric k) (T k).tube.carrier
      ((H.segment k).path (H.segment k).lower) ((H.segment k).path b) = _
  have h := hmin k (H.segment k).lower b
        ⟨le_rfl, (H.segment k).lower_lt_upper.le⟩ hb hb.1
  have hfinite : (H.normalizedSliceMetric k).pathELength (H.segment k).path
      (H.segment k).lower b ≠ ⊤ := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) :
        ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier → Type _) :=
      ⟨(H.normalizedSliceMetric k).toRiemannianMetric⟩
    have hfull := H.normalizedSlice_path_length_lt k
    exact ne_top_of_le_ne_top (ne_top_of_lt hfull)
      (Manifold.pathELength_mono le_rfl hb.2)
  rw [← h]
  exact (ENNReal.ofReal_toReal hfinite).symm

end PoincareConjecture.M28.CounterexampleNeckFamily
