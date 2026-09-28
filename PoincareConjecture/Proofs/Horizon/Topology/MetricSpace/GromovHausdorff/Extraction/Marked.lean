import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.MarkedRealization
import Mathlib.Topology.MetricSpace.GromovHausdorff

open Set Filter Topology
open scoped Topology NNReal ENNReal lp

noncomputable section

namespace Poincare.GromovHausdorff

universe u

private theorem ghDist_tendsto_zero_of_toGHSpace_tendsto
    (A : ℕ → FiniteDiameterBasedMetricSpace.{0})
    [∀ n, CompactSpace (A n).carrier]
    {p : _root_.GromovHausdorff.GHSpace}
    (hgh : Tendsto
      (fun n => _root_.GromovHausdorff.toGHSpace (A n).carrier)
      atTop (𝓝 p)) :
    Tendsto
      (fun n => _root_.GromovHausdorff.ghDist (A n).carrier p.Rep)
      atTop (𝓝 0) := by
  have hdist : Tendsto
      (fun n => dist (_root_.GromovHausdorff.toGHSpace (A n).carrier) p)
      atTop (𝓝 0) := by
    simpa only [dist_self] using
      (hgh.dist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)))
  simpa [_root_.GromovHausdorff.ghDist,
    _root_.GromovHausdorff.GHSpace.toGHSpace_rep] using hdist

private theorem exists_coupling_data
    (A : ℕ → FiniteDiameterBasedMetricSpace.{0})
    [∀ n, CompactSpace (A n).carrier]
    (p : _root_.GromovHausdorff.GHSpace) :
    ∃ f : ∀ n, (A n).carrier → lp (fun _ : ℕ => ℝ) ∞,
      ∃ g : ∀ _, p.Rep → lp (fun _ : ℕ => ℝ) ∞,
        (∀ n, Isometry (f n)) ∧
        (∀ n, Isometry (g n)) ∧
        (∀ n, _root_.GromovHausdorff.ghDist (A n).carrier p.Rep =
          Metric.hausdorffDist (Set.range (f n)) (Set.range (g n))) := by
  have hcouple : ∀ n, ∃ f : (A n).carrier → lp (fun _ : ℕ => ℝ) ∞,
      ∃ g : p.Rep → lp (fun _ : ℕ => ℝ) ∞,
        Isometry f ∧ Isometry g ∧
          _root_.GromovHausdorff.ghDist (A n).carrier p.Rep =
            Metric.hausdorffDist (Set.range f) (Set.range g) := by
    intro n
    simpa using
      (_root_.GromovHausdorff.ghDist_eq_hausdorffDist
        (A n).carrier p.Rep)
  choose f g hfg using hcouple
  refine ⟨f, g, ?_, ?_, ?_⟩
  · intro n
    exact (hfg n).1
  · intro n
    exact (hfg n).2.1
  · intro n
    exact (hfg n).2.2

private theorem exists_subseq_marked_displacement
    (A : ℕ → FiniteDiameterBasedMetricSpace.{0})
    [∀ n, CompactSpace (A n).carrier]
    (p : _root_.GromovHausdorff.GHSpace)
    {E : Type} [NormedAddCommGroup E]
    (f : ∀ n, (A n).carrier → E)
    (g : ∀ _, p.Rep → E)
    (hf : ∀ n, Isometry (f n))
    (hg : ∀ n, Isometry (g n))
    (herr : Tendsto
      (fun n => Metric.hausdorffDist (Set.range (f n)) (Set.range (g n)))
      atTop (𝓝 0)) :
    ∃ q : p.Rep, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto
        (fun n => dist (f (φ n) (A (φ n)).base) (g (φ n) q))
        atTop (𝓝 0) := by
  have hnear_exists (n : ℕ) :
      ∃ q : p.Rep,
        dist (f n (A n).base) (g n q) ≤
          Metric.hausdorffDist (Set.range (f n)) (Set.range (g n)) := by
    have hfin : Metric.hausdorffEDist (Set.range (f n))
        (Set.range (g n)) ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (Set.range_nonempty (f n)) (Set.range_nonempty (g n))
        (isCompact_range (hf n).continuous).isBounded
        (isCompact_range (hg n).continuous).isBounded
    obtain ⟨z, hz, hzeq⟩ :=
      (isCompact_range (hg n).continuous).exists_infDist_eq_dist
        (Set.range_nonempty (g n)) (f n (A n).base)
    rcases hz with ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    rw [← hzeq]
    exact Metric.infDist_le_hausdorffDist_of_mem
      (Set.mem_range_self (A n).base) hfin
  let near : ℕ → p.Rep := fun n => Classical.choose (hnear_exists n)
  have hnear (n : ℕ) :
      dist (f n (A n).base) (g n (near n)) ≤
        Metric.hausdorffDist (Set.range (f n)) (Set.range (g n)) :=
    Classical.choose_spec (hnear_exists n)
  obtain ⟨q, _, φ, hφ, hqconv⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set p.Rep)).tendsto_subseq
      (fun n => Set.mem_univ (near n))
  have hnear_zero : Tendsto
      (fun n => dist (f (φ n) (A (φ n)).base)
        (g (φ n) (near (φ n)))) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact hnear (φ n)
    · simpa [Function.comp_def] using herr.comp hφ.tendsto_atTop
  have hqdist : Tendsto (fun n => dist (near (φ n)) q)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_iff_dist_tendsto_zero.mp hqconv)
  refine ⟨q, φ, hφ, ?_⟩
  apply squeeze_zero
  · intro n
    exact dist_nonneg
  · intro n
    calc
      dist (f (φ n) (A (φ n)).base) (g (φ n) q) ≤
          dist (f (φ n) (A (φ n)).base)
              (g (φ n) (near (φ n))) +
            dist (g (φ n) (near (φ n))) (g (φ n) q) :=
        dist_triangle _ _ _
      _ = dist (f (φ n) (A (φ n)).base)
              (g (φ n) (near (φ n))) +
            dist (near (φ n)) q := by
        rw [(hg (φ n)).dist_eq]
  · simpa using hnear_zero.add hqdist

private theorem exists_translated_realization_sequence
    (A : ℕ → FiniteDiameterBasedMetricSpace.{0})
    (Y : FiniteDiameterBasedMetricSpace.{0})
    [∀ n, CompactSpace (A n).carrier] [CompactSpace Y.carrier]
    {E : Type} [NormedAddCommGroup E]
    (f : ∀ n, (A n).carrier → E)
    (g : ∀ _, Y.carrier → E)
    (hf : ∀ n, Isometry (f n))
    (hg : ∀ n, Isometry (g n))
    (herr : Tendsto
      (fun n => Metric.hausdorffDist (Set.range (f n)) (Set.range (g n)))
      atTop (𝓝 0))
    (hbase : Tendsto
      (fun n => dist (f n (A n).base) (g n Y.base))
      atTop (𝓝 0)) :
    ∃ S : VaryingRealizationSequence
        (fun n => (A n).toBasedMetricSpaceBundle)
        Y.toBasedMetricSpaceBundle,
      Tendsto
        (fun n => @Metric.hausdorffDist (S.ambient n).carrier inferInstance
          (Set.range (S.left n)) (Set.range (S.right n)))
        atTop (𝓝 0) := by
  let S : VaryingRealizationSequence
      (fun n => (A n).toBasedMetricSpaceBundle)
      Y.toBasedMetricSpaceBundle :=
    { ambient := fun _ =>
        { carrier := E
          metric := inferInstance }
      left := f
      right := fun n y =>
        (f n (A n).base - g n Y.base) +ᵥ g n y
      left_isometry := hf
      right_isometry := fun n =>
        (isometry_vadd E (f n (A n).base - g n Y.base)).comp (hg n)
      base_agree := fun n => by
        change f n (A n).base =
          (f n (A n).base - g n Y.base) + g n Y.base
        exact (sub_add_cancel _ _).symm
      hausdorff_tendsto_zero := by
        apply squeeze_zero
        · intro n
          exact Metric.hausdorffDist_nonneg
        · intro n
          exact hausdorffDist_translatedMap_comp_le
            (f n) (g n) (hf n) (hg n) (A n).base Y.base
        · simpa [Function.comp_def] using herr.add hbase }
  refine ⟨S, ?_⟩
  exact S.hausdorff_tendsto_zero

theorem exists_subseq_marked_fixed_radius_realization
    (A : ℕ → FiniteDiameterBasedMetricSpace.{0})
    [∀ n, CompactSpace (A n).carrier]
    (hbounded : UniformlyBoundedDiameter A)
    (p : _root_.GromovHausdorff.GHSpace)
    (hgh : Tendsto
      (fun n => _root_.GromovHausdorff.toGHSpace (A n).carrier)
      atTop (𝓝 p)) :
    ∃ φ : ℕ → ℕ, ∃ Y : PointedCompactMetricSpace.{0},
      StrictMono φ ∧ Y.carrier = p.Rep ∧
      ∃ S : VaryingRealizationSequence
          (fun n => (A (φ n)).toBasedMetricSpaceBundle)
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace Y).toBasedMetricSpaceBundle,
        Tendsto
          (fun n => @Metric.hausdorffDist (S.ambient n).carrier inferInstance
            (Set.range (S.left n)) (Set.range (S.right n)))
          atTop (𝓝 0) ∧
        PointedGHConverges
          (fun n => A (φ n))
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace Y) := by
  classical
  obtain ⟨f, g, hf, hg, hfg⟩ := exists_coupling_data A p
  have herr : Tendsto
      (fun n => Metric.hausdorffDist (Set.range (f n)) (Set.range (g n)))
      atTop (𝓝 0) := by
    have hdist := ghDist_tendsto_zero_of_toGHSpace_tendsto A hgh
    convert hdist using 1
    funext n
    exact (hfg n).symm
  obtain ⟨q, φ, hφ, hbase⟩ :=
    exists_subseq_marked_displacement A p f g hf hg herr
  let Y : PointedCompactMetricSpace :=
    { carrier := p.Rep
      metric := inferInstance
      compact := inferInstance
      nonempty := inferInstance
      base := q }
  let Yfd : FiniteDiameterBasedMetricSpace :=
    PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace Y
  letI : CompactSpace Yfd.carrier := by
    change CompactSpace p.Rep
    infer_instance
  obtain ⟨S, hS⟩ :=
    exists_translated_realization_sequence
      (A := fun n => A (φ n)) (Y := Yfd)
      (f := fun n => f (φ n)) (g := fun n => g (φ n))
      (hf := fun n => hf (φ n)) (hg := fun n => hg (φ n))
      (herr := by
        convert herr.comp hφ.tendsto_atTop using 1
        all_goals rfl)
      (hbase := by
        change Tendsto
          (fun n => dist (f (φ n) (A (φ n)).base) (g (φ n) q))
          atTop (𝓝 0)
        exact hbase)
  have hbounded' : UniformlyBoundedDiameter (fun n => A (φ n)) := by
    obtain ⟨C, hC⟩ := hbounded
    exact ⟨C, fun n x y => hC (φ n) x y⟩
  have hpointed : PointedGHConverges (fun n => A (φ n)) Yfd :=
    pointedGHConverges_of_realizationSequence
      (fun n => A (φ n)) Yfd hbounded' S
  refine ⟨φ, Y, hφ, rfl, ?_⟩
  refine ⟨S, ?_, ?_⟩
  · simpa [Yfd] using hS
  · simpa [Yfd] using hpointed

theorem exists_common_subseq_marked_realizations
    (A : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{0})
    [∀ i n, CompactSpace (A i n).carrier]
    (hbounded : ∀ i, UniformlyBoundedDiameter (A i))
    (p : ℕ → _root_.GromovHausdorff.GHSpace)
    (hgh : ∀ i, Tendsto
      (fun n => _root_.GromovHausdorff.toGHSpace (A i n).carrier)
      atTop (𝓝 (p i))) :
    ∃ φ : ℕ → ℕ, ∃ Y : ℕ → PointedCompactMetricSpace.{0},
      StrictMono φ ∧
      (∀ i, (Y i).carrier = (p i).Rep) ∧
      ∀ i, ∃ S : VaryingRealizationSequence
          (fun n => (A i (φ n)).toBasedMetricSpaceBundle)
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
            (Y i)).toBasedMetricSpaceBundle,
        Tendsto
          (fun n => @Metric.hausdorffDist (S.ambient n).carrier inferInstance
            (Set.range (S.left n)) (Set.range (S.right n)))
          atTop (𝓝 0) ∧
        PointedGHConverges
          (fun n => A i (φ n))
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace (Y i)) := by
  classical
  have hcouple : ∀ i, ∃ f : ∀ n, (A i n).carrier →
      lp (fun _ : ℕ => ℝ) ∞,
      ∃ g : ∀ _, (p i).Rep → lp (fun _ : ℕ => ℝ) ∞,
        (∀ n, Isometry (f n)) ∧
        (∀ n, Isometry (g n)) ∧
        (∀ n, _root_.GromovHausdorff.ghDist (A i n).carrier (p i).Rep =
          Metric.hausdorffDist (Set.range (f n)) (Set.range (g n))) :=
    fun i => exists_coupling_data (A i) (p i)
  choose f g hfg using hcouple
  have hf : ∀ i n, Isometry (f i n) := fun i => (hfg i).1
  have hg : ∀ i n, Isometry (g i n) := fun i => (hfg i).2.1
  have herr : ∀ i, Tendsto
      (fun n => Metric.hausdorffDist
        (Set.range (f i n)) (Set.range (g i n)))
      atTop (𝓝 0) := by
    intro i
    have hdist := ghDist_tendsto_zero_of_toGHSpace_tendsto (A i) (hgh i)
    convert hdist using 1
    funext n
    exact ((hfg i).2.2 n).symm
  have hnear_exists (i n : ℕ) :
      ∃ q : (p i).Rep,
        dist (f i n (A i n).base) (g i n q) ≤
          Metric.hausdorffDist (Set.range (f i n)) (Set.range (g i n)) := by
    have hfin : Metric.hausdorffEDist (Set.range (f i n))
        (Set.range (g i n)) ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (Set.range_nonempty (f i n)) (Set.range_nonempty (g i n))
        (isCompact_range (hf i n).continuous).isBounded
        (isCompact_range (hg i n).continuous).isBounded
    obtain ⟨z, hz, hzeq⟩ :=
      (isCompact_range (hg i n).continuous).exists_infDist_eq_dist
        (Set.range_nonempty (g i n)) (f i n (A i n).base)
    rcases hz with ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    rw [← hzeq]
    exact Metric.infDist_le_hausdorffDist_of_mem
      (Set.mem_range_self (A i n).base) hfin
  choose near hnear using hnear_exists
  let marked : ℕ → ∀ i, (p i).Rep := fun n i => near i n
  obtain ⟨q, φ, hφ, hqconv⟩ := CompactSpace.tendsto_subseq marked
  let Y : ℕ → PointedCompactMetricSpace := fun i =>
    { carrier := (p i).Rep
      metric := inferInstance
      compact := inferInstance
      nonempty := inferInstance
      base := q i }
  refine ⟨φ, Y, hφ, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    let Yfd : FiniteDiameterBasedMetricSpace :=
      PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace (Y i)
    letI : CompactSpace Yfd.carrier := by
      change CompactSpace (p i).Rep
      infer_instance
    have hnear_zero : Tendsto
        (fun n => dist (f i (φ n) (A i (φ n)).base)
          (g i (φ n) (near i (φ n))))
        atTop (𝓝 0) := by
      apply squeeze_zero
      · intro n
        exact dist_nonneg
      · intro n
        exact hnear i (φ n)
      · simpa [Function.comp_def] using (herr i).comp hφ.tendsto_atTop
    have hqconv_i : Tendsto (fun n => near i (φ n)) atTop (𝓝 (q i)) := by
      simpa [marked, Function.comp_def] using
        (continuousAt_apply i q).tendsto.comp hqconv
    have hqdist : Tendsto (fun n => dist (near i (φ n)) (q i))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (tendsto_iff_dist_tendsto_zero.mp hqconv_i)
    have hbase : Tendsto
        (fun n => dist (f i (φ n) (A i (φ n)).base)
          (g i (φ n) (q i))) atTop (𝓝 0) := by
      apply squeeze_zero
      · intro n
        exact dist_nonneg
      · intro n
        calc
          dist (f i (φ n) (A i (φ n)).base) (g i (φ n) (q i)) ≤
              dist (f i (φ n) (A i (φ n)).base)
                  (g i (φ n) (near i (φ n))) +
                dist (g i (φ n) (near i (φ n)))
                  (g i (φ n) (q i)) :=
            dist_triangle _ _ _
          _ = dist (f i (φ n) (A i (φ n)).base)
                  (g i (φ n) (near i (φ n))) +
                dist (near i (φ n)) (q i) := by
              rw [(hg i (φ n)).dist_eq]
      · simpa using hnear_zero.add hqdist
    obtain ⟨S, hS⟩ :=
      exists_translated_realization_sequence
        (A := fun n => A i (φ n)) (Y := Yfd)
        (f := fun n => f i (φ n)) (g := fun n => g i (φ n))
        (hf := fun n => hf i (φ n)) (hg := fun n => hg i (φ n))
        (herr := by
          convert (herr i).comp hφ.tendsto_atTop using 1
          all_goals rfl)
        (hbase := hbase)
    have hbounded' : UniformlyBoundedDiameter (fun n => A i (φ n)) := by
      obtain ⟨C, hC⟩ := hbounded i
      exact ⟨C, fun n x y => hC (φ n) x y⟩
    have hpointed : PointedGHConverges (fun n => A i (φ n)) Yfd :=
      pointedGHConverges_of_realizationSequence
        (fun n => A i (φ n)) Yfd hbounded' S
    refine ⟨S, ?_, ?_⟩
    · simpa [Yfd] using hS
    · simpa [Yfd] using hpointed

end Poincare.GromovHausdorff
