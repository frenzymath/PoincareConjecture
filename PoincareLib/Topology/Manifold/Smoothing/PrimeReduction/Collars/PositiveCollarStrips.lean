import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.CompactClosedStrip
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.InducedOpenImage

/-!
# Uniform whole positive collar strips

The compact zero section gives a closed one-sided strip inside an
actual open part of the range. Every smaller half-open strip is open
in the target, including time zero. See PrimeReduction017, section2.
-/

set_option autoImplicit false

open Set

local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

variable {A X : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace X]

/-- The entire compact zero section has a uniform closed positive
strip in its prescribed open neighborhood. See017, section2. -/
theorem Continuous.exists_closed_positive_strip_subset {f : A × I → X}
    (hf : Continuous f) {W : Set X} (hW : IsOpen W)
    (hzero : ∀ a : A, f (a, ⟨0, le_rfl, zero_le_one⟩) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (a : A) (t : I), (t : ℝ) ≤ δ → f (a, t) ∈ W := by
  let u : A × J → A × I := fun z =>
    (z.1, ⟨|(z.2 : ℝ)|, abs_nonneg _, abs_le.mpr z.2.property⟩)
  have hu : Continuous u := by
    apply Continuous.prodMk continuous_fst
    exact (continuous_abs.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hbase (a : A) : (f ∘ u) (a, ⟨0, by norm_num⟩) ∈ W := by
    simpa [u] using hzero a
  obtain ⟨δ, hδ, hδsmall, hstrip⟩ :=
    (hf.comp hu).exists_closed_strip_subset hW hbase
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro a t ht
  have htJ : (t : ℝ) ∈ J := ⟨by linarith [t.property.1], t.property.2⟩
  have htδ : |(t : ℝ)| ≤ δ := by rwa [abs_of_nonneg t.property.1]
  have h := hstrip a ⟨t, htJ⟩ htδ
  simpa [u, abs_of_nonneg t.property.1] using h

/-- A compact positive product whose range contains an actual open
neighborhood of its base has whole relatively open small strips.
The closed strip stays in that same neighborhood. See017, section2. -/
theorem Topology.IsEmbedding.exists_positive_collar_strips {f : A × I → X}
    (hf : Topology.IsEmbedding f) {W : Set X} (hW : IsOpen W)
    (hzero : ∀ a : A, f (a, ⟨0, le_rfl, zero_le_one⟩) ∈ W)
    (hWrange : W ⊆ range f) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ (a : A) (t : I), (t : ℝ) ≤ δ → f (a, t) ∈ W) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen (f '' {z : A × I | (z.2 : ℝ) < ε}) := by
  obtain ⟨δ, hδ, hδsmall, hstrip⟩ :=
    hf.continuous.exists_closed_positive_strip_subset hW hzero
  refine ⟨δ, hδ, hδsmall, hstrip, ?_⟩
  intro ε _ hεδ
  have hopen : IsOpen {z : A × I | (z.2 : ℝ) < ε} :=
    isOpen_Iio.preimage (continuous_subtype_val.comp continuous_snd)
  apply hf.isInducing.isOpen_image_of_subset_open hopen hW _ hWrange
  rintro _ ⟨z, hz, rfl⟩
  exact hstrip z.1 z.2 (le_trans (le_of_lt hz) hεδ)
