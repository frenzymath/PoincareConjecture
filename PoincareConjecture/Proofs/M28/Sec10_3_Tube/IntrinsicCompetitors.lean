import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.SpecificLimits.Basic












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]



theorem exists_unit_interval_path (g : RiemannianMetric 3 M)
    {U : Set M} {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 = g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let η : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap a b
  have hη : MapsTo η (Icc (0 : ℝ) 1) (Icc a b) := by
    change Icc (0 : ℝ) 1 ⊆ η ⁻¹' Icc a b
    rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    simp [hab]
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (γ ∘ η) (Icc (0 : ℝ) 1) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · exact hη
  have hdiff : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) γ (Icc (η 0) (η 1)) := by
    simpa [η, ContinuousAffineMap.coe_lineMap_eq] using
      hγ.mdifferentiableOn one_ne_zero
  refine ⟨γ ∘ η, ?_, ?_, hsmooth, hγU.comp hη, ?_⟩
  · simp [η, ContinuousAffineMap.coe_lineMap_eq]
  · simp [η, ContinuousAffineMap.coe_lineMap_eq]
  · have hmono : MonotoneOn (η : ℝ → ℝ) (Icc (0 : ℝ) 1) := by
      simpa only [η, ContinuousAffineMap.coe_lineMap_eq] using
        (AffineMap.lineMap_mono hab).monotoneOn (Icc (0 : ℝ) 1)
    have heq := Manifold.pathELength_comp_of_monotoneOn
      (I := 𝓡 3) (γ := γ) (f := (η : ℝ → ℝ)) zero_le_one
      hmono η.differentiableOn hdiff
    change Manifold.pathELength (𝓡 3) (γ ∘ η) 0 1 =
      Manifold.pathELength (𝓡 3) γ a b
    simpa [η, ContinuousAffineMap.coe_lineMap_eq] using heq



theorem intrinsicEDist_le_pathELength (g : RiemannianMetric 3 M)
    {U : Set M} {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U) :
    intrinsicEDist g U (γ a) (γ b) ≤ g.pathELength γ a b := by
  obtain ⟨σ, h0, h1, hσ, hσU, hlength⟩ :=
    exists_unit_interval_path g hab hγ hγU
  rw [← hlength]
  apply sInf_le
  refine ⟨σ, hσ, h0, h1, ?_, rfl⟩
  rintro x ⟨t, ht, rfl⟩
  exact hσU ht



theorem exists_intrinsic_competitor (g : RiemannianMetric 3 M)
    {U : Set M} {p q : M} {l : ℝ≥0∞}
    (hl : intrinsicEDist g U p q < l) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) U ∧ g.pathELength γ 0 1 < l := by
  rw [intrinsicEDist] at hl
  obtain ⟨L, ⟨γ, hγ, h0, h1, hU, rfl⟩, hL⟩ := sInf_lt_iff.mp hl
  exact ⟨γ, h0, h1, hγ, fun t ht => hU ⟨t, ht, rfl⟩, hL⟩




theorem exists_intrinsic_minimizing_sequence_of_path (g : RiemannianMetric 3 M)
    {U : Set M} {γ : ℝ → M} {a b L : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hlen : g.pathELength γ a b < ENNReal.ofReal L) :
    ∃ σ : ℕ → ℝ → M,
      (∀ k, σ k 0 = γ a ∧ σ k 1 = γ b ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (σ k) (Icc (0 : ℝ) 1) ∧
        MapsTo (σ k) (Icc (0 : ℝ) 1) U ∧
        g.pathELength (σ k) 0 1 < ENNReal.ofReal L) ∧
      Tendsto (fun k => g.pathELength (σ k) 0 1) atTop
        (𝓝 (intrinsicEDist g U (γ a) (γ b))) := by
  have hupper : intrinsicEDist g U (γ a) (γ b) < ENNReal.ofReal L :=
    (intrinsicEDist_le_pathELength g hab hγ hγU).trans_lt hlen
  have hfinite : intrinsicEDist g U (γ a) (γ b) ≠ ⊤ :=
    ne_top_of_lt (hupper.trans_le le_top)
  have happrox (k : ℕ) : intrinsicEDist g U (γ a) (γ b) <
      ENNReal.ofReal ((intrinsicEDist g U (γ a) (γ b)).toReal +
        1 / ((k : ℝ) + 1)) := by
    apply (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  choose σ h0 h1 hσ hσU hσlen using
    fun k => exists_intrinsic_competitor g (lt_min hupper (happrox k))
  refine ⟨σ, fun k => ⟨h0 k, h1 k, hσ k, hσU k,
    (hσlen k).trans_le (min_le_left _ _)⟩, ?_⟩
  have ht : Tendsto (fun k : ℕ =>
      ENNReal.ofReal ((intrinsicEDist g U (γ a) (γ b)).toReal +
        1 / ((k : ℝ) + 1))) atTop
      (𝓝 (intrinsicEDist g U (γ a) (γ b))) := by
    have h : Tendsto (fun k : ℕ =>
        ENNReal.ofReal ((intrinsicEDist g U (γ a) (γ b)).toReal +
          1 / ((k : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal ((intrinsicEDist g U (γ a) (γ b)).toReal + 0))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (intrinsicEDist g U (γ a) (γ b)).toReal)).add
          tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [add_zero, ENNReal.ofReal_toReal hfinite] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro k
    simpa only [h0 k, h1 k] using
      intrinsicEDist_le_pathELength g zero_le_one (hσ k) (hσU k)
  · intro k
    exact ((hσlen k).trans_le (min_le_right _ _)).le

end PoincareConjecture.M28
