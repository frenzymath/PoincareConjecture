import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import PoincareConjecture.Proofs.M58.Mathlib.CompactRiemannianBallBundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m60PeriodicLoop_velocity (γ : C1FreeLoopSpace (M := M)) (t : ℝ) :
    curveVelocity (periodicFreeLoop γ) t =
      mfderiv (𝓡 2) (𝓡 3) γ.extension (angularPoint t)
        (loopCircleTangent ⟨angularPoint t, norm_angularPoint t⟩) := by
  have hγ := γ.regularity.contMDiffAt
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const) |>.mem_nhds
        (angularPoint_mem_annulus t))
  have hd := mfderiv_comp_apply t (hγ.mdifferentiableAt one_ne_zero)
    (hasDerivAt_angularPoint t).differentiableAt.mdifferentiableAt (1 : ℝ)
  have hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) angularPoint t 1 = angularVector t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv]
      using! (hasDerivAt_angularPoint t).deriv
  erw [hv] at hd
  exact hd

theorem m60_continuous_loop_tangentNorm (g : RiemannianMetric 3 M) :
    Continuous (fun p : C1FreeLoopSpace (M := M) × LoopCircle =>
      g.tangentNorm (p.1 p.2) (c1LoopTangent p.1 p.2).2) := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact continuous_bundle_norm.comp continuous_loop_tangent_eval

theorem m60_exists_loop_length_neighborhood (g : RiemannianMetric 3 M)
    (γ₀ : C1FreeLoopSpace (M := M)) :
    ∃ (U : Set (C1FreeLoopSpace (M := M))) (L : ℝ),
      IsOpen U ∧ γ₀ ∈ U ∧ 0 ≤ L ∧ ∀ γ ∈ U, freeLoopLength g γ ≤ L := by
  let S := fun p : C1FreeLoopSpace (M := M) × LoopCircle =>
    g.tangentNorm (p.1 p.2) (c1LoopTangent p.1 p.2).2
  have hS : Continuous S := m60_continuous_loop_tangentNorm g
  obtain ⟨B, hB⟩ :=
    (isCompact_univ : IsCompact (univ : Set LoopCircle)).exists_bound_of_continuousOn
      (hS.comp (continuous_const.prodMk continuous_id)).continuousOn
  let K := max B 0 + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound : ({γ₀} : Set (C1FreeLoopSpace (M := M))) ×ˢ univ ⊆ {p | S p < K} := by
    rintro ⟨γ, z⟩ ⟨hγ, _⟩
    have heq : γ = γ₀ := hγ
    subst γ
    have hz := hB z (mem_univ z)
    have hz' : S (γ₀, z) ≤ B := (le_abs_self _).trans hz
    exact hz'.trans_lt (lt_of_le_of_lt (le_max_left B 0) (by dsimp [K]; linarith))
  obtain ⟨U, V, hU, _, hγ₀, hV, hUV⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ (isOpen_lt hS continuous_const) hbound
  refine ⟨U, rampPeriod * K, hU, hγ₀ (mem_singleton γ₀), ?_, ?_⟩
  · exact mul_nonneg (by dsimp [rampPeriod]; positivity) hK
  · intro γ hγ
    have hs : ∀ t : ℝ, g.tangentNorm (periodicFreeLoop γ t)
        (curveVelocity (periodicFreeLoop γ) t) ≤ K := by
      intro t
      have hb := hUV (a := (γ, ⟨angularPoint t, norm_angularPoint t⟩))
        ⟨hγ, hV (mem_univ (⟨angularPoint t, norm_angularPoint t⟩ : LoopCircle))⟩
      rw [m60PeriodicLoop_velocity]
      have heq := γ.boundary ⟨angularPoint t, norm_angularPoint t⟩
      change γ.extension (angularPoint t) = γ ⟨angularPoint t, norm_angularPoint t⟩ at heq
      change g.tangentNorm (γ.extension (angularPoint t)) _ ≤ K
      rw [heq]
      exact le_of_lt hb
    have hi := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
      (a := 0) (b := rampPeriod)
      (by dsimp [rampPeriod]; positivity)
      ((continuous_freeLoopSpeed g γ).intervalIntegrable 0 rampPeriod)
      (continuous_const.intervalIntegrable 0 rampPeriod) hs
    simpa +instances only [freeLoopLength, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul] using! hi

theorem m60_exists_loop_close_neighborhood [T2Space M] (g : RiemannianMetric 3 M)
    (γ₀ : C1FreeLoopSpace (M := M)) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ U : Set (C1FreeLoopSpace (M := M)), IsOpen U ∧ γ₀ ∈ U ∧
      ∀ γ ∈ U, ∀ z : LoopCircle, g.edist (γ z) (γ₀ z) < ENNReal.ofReal delta := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 3) M
  let W := {p : C1FreeLoopSpace (M := M) × LoopCircle |
    g.edist (p.1 p.2) (γ₀ p.2) < ENNReal.ofReal delta}
  have hW : IsOpen W := isOpen_lt
    (continuous_loop_eval.edist (γ₀.continuous.comp continuous_snd)) continuous_const
  have hbase : ({γ₀} : Set (C1FreeLoopSpace (M := M))) ×ˢ univ ⊆ W := by
    rintro ⟨γ, z⟩ ⟨hγ, _⟩
    have heq : γ = γ₀ := hγ
    subst γ
    change edist (γ₀ z) (γ₀ z) < ENNReal.ofReal delta
    simpa only [edist_self] using (ENNReal.ofReal_pos.mpr hdelta)
  obtain ⟨U, V, hU, _, hγ₀, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hW hbase
  exact ⟨U, hU, hγ₀ (mem_singleton γ₀),
    fun γ hγ z => hUV (a := (γ, z)) ⟨hγ, hV (mem_univ z)⟩⟩

end PoincareConjecture
