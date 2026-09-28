import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Distance
import Mathlib.Topology.MetricSpace.GromovHausdorff

open Set TopologicalSpace Metric Function KuratowskiEmbedding Filter
open scoped Topology NNReal ENNReal lp

noncomputable section

namespace Poincare.GromovHausdorff

universe u v w

def centeredKuratowskiMap
    {Z : Type v} [MetricSpace Z] [SeparableSpace Z]
    (z0 : Z) : Z -> lp (fun _ : ℕ => ℝ) ∞ :=
  fun z => kuratowskiEmbedding Z z - kuratowskiEmbedding Z z0

theorem centeredKuratowskiMap_isometry
    {Z : Type v} [MetricSpace Z] [SeparableSpace Z]
    (z0 : Z) :
    Isometry (centeredKuratowskiMap z0) := by
  apply Isometry.of_dist_eq
  intro x y
  simp [centeredKuratowskiMap, (kuratowskiEmbedding.isometry Z).dist_eq]

@[simp]
theorem centeredKuratowskiMap_self
    {Z : Type v} [MetricSpace Z] [SeparableSpace Z]
    (z0 : Z) :
    centeredKuratowskiMap z0 z0 = 0 := by
  simp [centeredKuratowskiMap]

theorem dist_sub_sub_le_additive
    {E : Type v} [NormedAddCommGroup E]
    (a b c d : E) :
    dist (a - b) (c - d) <= dist a c + dist b d := by
  calc
    dist (a - b) (c - d) <=
        dist (a - b) (a - d) + dist (a - d) (c - d) :=
      dist_triangle _ _ _
    _ = dist b d + dist a c := by
      rw [dist_sub_left, dist_sub_right]
    _ = dist a c + dist b d := add_comm _ _

theorem hausdorffDist_centeredKuratowski_comp_le
    {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    [MetricSpace Z] [SeparableSpace Z]
    (f : X -> Z) (g : Y -> Z)
    (hf : Isometry f) (hg : Isometry g)
    (xb : X) (yb : Y) :
    Metric.hausdorffDist
        (Set.range (centeredKuratowskiMap (f xb) ∘ f))
        (Set.range (centeredKuratowskiMap (g yb) ∘ g)) <=
      Metric.hausdorffDist (Set.range f) (Set.range g) + dist (f xb) (g yb) := by
  have hfin : Metric.hausdorffEDist (Set.range f) (Set.range g) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (Set.range_nonempty f) (Set.range_nonempty g)
      (isCompact_range hf.continuous).isBounded
      (isCompact_range hg.continuous).isBounded
  have hnonneg :
      0 <= Metric.hausdorffDist (Set.range f) (Set.range g) + dist (f xb) (g yb) :=
    add_nonneg Metric.hausdorffDist_nonneg dist_nonneg
  apply Metric.hausdorffDist_le_of_mem_dist hnonneg
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hyeq⟩ :=
      (isCompact_range hg.continuous).exists_infDist_eq_dist
        (Set.range_nonempty g) (f x)
    obtain ⟨y0, hy0⟩ := hy
    refine ⟨centeredKuratowskiMap (g yb) (g y0), ⟨y0, rfl⟩, ?_⟩
    calc
      dist (centeredKuratowskiMap (f xb) (f x))
          (centeredKuratowskiMap (g yb) (g y0)) <=
          dist (f x) (g y0) + dist (f xb) (g yb) := by
        dsimp [centeredKuratowskiMap]
        exact (dist_sub_sub_le_additive _ _ _ _).trans_eq <| by
          rw [(kuratowskiEmbedding.isometry Z).dist_eq,
            (kuratowskiEmbedding.isometry Z).dist_eq]
      _ <= Metric.hausdorffDist (Set.range f) (Set.range g) +
          dist (f xb) (g yb) := by
        gcongr
        rw [hy0, ← hyeq]
        exact Metric.infDist_le_hausdorffDist_of_mem
          (Set.mem_range_self x) hfin
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx, hxeq⟩ :=
      (isCompact_range hf.continuous).exists_infDist_eq_dist
        (Set.range_nonempty f) (g y)
    obtain ⟨x0, hx0⟩ := hx
    refine ⟨centeredKuratowskiMap (f xb) (f x0), ⟨x0, rfl⟩, ?_⟩
    calc
      dist (centeredKuratowskiMap (g yb) (g y))
          (centeredKuratowskiMap (f xb) (f x0)) =
          dist (centeredKuratowskiMap (f xb) (f x0))
            (centeredKuratowskiMap (g yb) (g y)) := dist_comm _ _
      _ <=
          dist (f x0) (g y) + dist (f xb) (g yb) := by
        dsimp [centeredKuratowskiMap]
        exact (dist_sub_sub_le_additive _ _ _ _).trans_eq <| by
          rw [(kuratowskiEmbedding.isometry Z).dist_eq,
            (kuratowskiEmbedding.isometry Z).dist_eq]
      _ <= Metric.hausdorffDist (Set.range f) (Set.range g) +
          dist (f xb) (g yb) := by
        gcongr
        rw [hx0, dist_comm, ← hxeq]
        have hfin' : Metric.hausdorffEDist (Set.range g) (Set.range f) ≠ ⊤ := by
          simpa only [Metric.hausdorffEDist_comm] using hfin
        calc
          infDist (g y) (Set.range f) <=
              Metric.hausdorffDist (Set.range g) (Set.range f) :=
            Metric.infDist_le_hausdorffDist_of_mem
              (Set.mem_range_self y) hfin'
          _ = Metric.hausdorffDist (Set.range f) (Set.range g) :=
            Metric.hausdorffDist_comm

noncomputable def centeredPointedGHRealization
    {X Y : FiniteDiameterBasedMetricSpace.{0}}
    {Z : Type} [MetricSpace Z] [SeparableSpace Z]
    (f : X.carrier -> Z) (g : Y.carrier -> Z)
    (hf : Isometry f) (hg : Isometry g) :
    PointedGHRealization X Y :=
  { ambient :=
      { carrier := lp (fun _ : ℕ => ℝ) ∞
        metric := inferInstance
        base := 0 }
    left := centeredKuratowskiMap (f X.base) ∘ f
    right := centeredKuratowskiMap (g Y.base) ∘ g
    left_isometry := (centeredKuratowskiMap_isometry (f X.base)).comp hf
    right_isometry := (centeredKuratowskiMap_isometry (g Y.base)).comp hg
    left_base := by simp [Function.comp_apply, centeredKuratowskiMap_self]
    right_base := by simp [Function.comp_apply, centeredKuratowskiMap_self] }

theorem pointedHausdorffDist_centeredPointedGHRealization_le
    {X Y : FiniteDiameterBasedMetricSpace.{0}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    {Z : Type} [MetricSpace Z] [SeparableSpace Z]
    (f : X.carrier -> Z) (g : Y.carrier -> Z)
    (hf : Isometry f) (hg : Isometry g) :
    pointedHausdorffDist (centeredPointedGHRealization f g hf hg) <=
      Metric.hausdorffDist (Set.range f) (Set.range g) +
        dist (f X.base) (g Y.base) := by
  exact hausdorffDist_centeredKuratowski_comp_le f g hf hg X.base Y.base

def translatedMap
    {E : Type u} [NormedAddCommGroup E]
    {X : Type v} (f : X -> E) (x0 : X) : X -> E :=
  fun x => f x - f x0

theorem translatedMap_isometry
    {E : Type u} [NormedAddCommGroup E]
    {X : Type v} [PseudoMetricSpace X]
    (f : X -> E) (x0 : X) (hf : Isometry f) :
    Isometry (translatedMap f x0) := by
  apply Isometry.of_dist_eq
  intro x y
  dsimp [translatedMap]
  rw [dist_sub_right, hf.dist_eq]

@[simp]
theorem translatedMap_self
    {E : Type u} [NormedAddCommGroup E]
    {X : Type v} (f : X -> E) (x0 : X) :
    translatedMap f x0 x0 = 0 := by
  simp [translatedMap]

theorem hausdorffDist_vadd_le
    {E : Type u} [NormedAddCommGroup E]
    {s t : Set E} (c : E)
    (hfin : Metric.hausdorffEDist s t ≠ ⊤) :
    Metric.hausdorffDist ((fun x : E => c +ᵥ x) '' s) t <=
      Metric.hausdorffDist s t + ‖c‖ := by
  let T : E -> E := fun x => c +ᵥ x
  have hT : Isometry T := isometry_vadd E c
  have hfinT : Metric.hausdorffEDist (T '' s) (T '' t) ≠ ⊤ := by
    simpa only [Metric.hausdorffEDist_image hT] using hfin
  have hshift : Metric.hausdorffDist (T '' t) t <= ‖c‖ := by
    apply Metric.hausdorffDist_le_of_mem_dist (norm_nonneg c)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simpa [T] using (dist_vadd_left c x)
    · rintro x hx
      refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
      simpa [T] using (dist_vadd_right c x)
  calc
    Metric.hausdorffDist (T '' s) t <=
        Metric.hausdorffDist (T '' s) (T '' t) +
          Metric.hausdorffDist (T '' t) t :=
      Metric.hausdorffDist_triangle hfinT
    _ = Metric.hausdorffDist s t + Metric.hausdorffDist (T '' t) t := by
      rw [Metric.hausdorffDist_image hT]
    _ <= Metric.hausdorffDist s t + ‖c‖ := by
      simpa [add_comm] using
        (add_le_add_left hshift (Metric.hausdorffDist s t))

theorem hausdorffDist_translatedMap_comp_le
    {X : Type u} {Y : Type v} {E : Type w}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    [NormedAddCommGroup E]
    (f : X -> E) (g : Y -> E)
    (hf : Isometry f) (hg : Isometry g)
    (xb : X) (yb : Y) :
    Metric.hausdorffDist
        (Set.range f)
        (Set.range (fun y => (f xb - g yb) +ᵥ g y)) <=
      Metric.hausdorffDist (Set.range f) (Set.range g) +
        dist (f xb) (g yb) := by
  have hfin : Metric.hausdorffEDist (Set.range f) (Set.range g) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (Set.range_nonempty f) (Set.range_nonempty g)
      (isCompact_range hf.continuous).isBounded
      (isCompact_range hg.continuous).isBounded
  have hc : ‖f xb - g yb‖ = dist (f xb) (g yb) := by
    rw [dist_eq_norm]
  have hfin' : Metric.hausdorffEDist (Set.range g) (Set.range f) ≠ ⊤ := by
    simpa only [Metric.hausdorffEDist_comm] using hfin
  have h := hausdorffDist_vadd_le
    (s := Set.range g) (t := Set.range f) (f xb - g yb) hfin'
  rw [hc] at h
  simpa only [Metric.hausdorffDist_comm, ← Set.range_comp, Function.comp_def] using h

noncomputable def translatedPointedGHRealization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    {E : Type u} [NormedAddCommGroup E]
    (f : X.carrier -> E) (g : Y.carrier -> E)
    (hf : Isometry f) (hg : Isometry g) :
    PointedGHRealization X Y :=
  { ambient :=
      { carrier := E
        metric := inferInstance
        base := f X.base }
    left := f
    right := fun y => (f X.base - g Y.base) +ᵥ g y
    left_isometry := hf
    right_isometry := (isometry_vadd E (f X.base - g Y.base)).comp hg
    left_base := rfl
    right_base := by
      change (f X.base - g Y.base) + g Y.base = f X.base
      exact sub_add_cancel _ _ }

theorem pointedHausdorffDist_translatedPointedGHRealization_le
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    {E : Type u} [NormedAddCommGroup E]
    (f : X.carrier -> E) (g : Y.carrier -> E)
    (hf : Isometry f) (hg : Isometry g) :
    pointedHausdorffDist (translatedPointedGHRealization f g hf hg) <=
      Metric.hausdorffDist (Set.range f) (Set.range g) +
        dist (f X.base) (g Y.base) := by
  exact hausdorffDist_translatedMap_comp_le f g hf hg X.base Y.base

theorem pointedGHDistance_le_ghDist_add_optimal_marked_displacement
    {X Y : FiniteDiameterBasedMetricSpace.{0}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier] :
    pointedGHDistance X Y ≤
      _root_.GromovHausdorff.ghDist X.carrier Y.carrier +
        dist
          (_root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base)
          (_root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base) := by
  let f := _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier
  let g := _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier
  let hf := _root_.GromovHausdorff.isometry_optimalGHInjl X.carrier Y.carrier
  let hg := _root_.GromovHausdorff.isometry_optimalGHInjr X.carrier Y.carrier
  let R := centeredPointedGHRealization f g hf hg
  calc
    pointedGHDistance X Y ≤ pointedHausdorffDist R :=
      pointedGHDistance_le_realization R
    _ ≤ Metric.hausdorffDist (Set.range f) (Set.range g) +
          dist (f X.base) (g Y.base) :=
      pointedHausdorffDist_centeredPointedGHRealization_le f g hf hg
    _ = _root_.GromovHausdorff.ghDist X.carrier Y.carrier +
          dist
            (_root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base)
            (_root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base) := by
      rw [_root_.GromovHausdorff.hausdorffDist_optimal]

theorem pointedGHConverges_of_ghDist_and_optimal_marked_displacement
    (X : ℕ → FiniteDiameterBasedMetricSpace.{0})
    (Y : FiniteDiameterBasedMetricSpace.{0})
    [∀ k, CompactSpace (X k).carrier] [CompactSpace Y.carrier]
    (hbounded : UniformlyBoundedDiameter X)
    (hgh : Tendsto
      (fun k => _root_.GromovHausdorff.ghDist (X k).carrier Y.carrier)
      atTop (𝓝 0))
    (hbase : Tendsto
      (fun k => dist
        (_root_.GromovHausdorff.optimalGHInjl (X k).carrier Y.carrier (X k).base)
        (_root_.GromovHausdorff.optimalGHInjr (X k).carrier Y.carrier Y.base))
      atTop (𝓝 0)) :
    PointedGHConverges X Y := by
  refine ⟨hbounded, ?_⟩
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg (X k) Y
  · intro k
    exact pointedGHDistance_le_ghDist_add_optimal_marked_displacement
      (X := X k) (Y := Y)
  · simpa using hgh.add hbase

end Poincare.GromovHausdorff
