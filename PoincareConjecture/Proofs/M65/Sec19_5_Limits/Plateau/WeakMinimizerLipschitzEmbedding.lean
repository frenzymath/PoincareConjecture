import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerExistence
import PoincareConjecture.Proofs.M40.Mathlib.RiemannianVectorNorm
import PoincareConjecture.Proofs.M01.NormalizationLocalDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ}

set_option maxHeartbeats 1200000 in

theorem m65Embedding_edist_bound (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (compact : IsCompact (univ : Set M)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ p q, edist (e p) (e q) ≤ (C : ℝ≥0∞) * g.edist p q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨c, _B, hc, _hB, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  have hroot : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  let C : ℝ≥0 := ⟨(Real.sqrt c)⁻¹, (inv_pos.mpr hroot).le⟩
  have hC : 0 < C := inv_pos.mpr hroot
  have hnorm (p : M) : ‖mfderiv (𝓡 3) (𝓡 N) e p‖ ≤ (C : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    intro v
    have hmetric := (hb p (mfderiv (𝓡 3) (𝓡 N) e p v)).1
    rw [m65EmbeddingMetric_image g e p (hinj p)] at hmetric
    change c * ‖(show EuclideanSpace ℝ (Fin N) from mfderiv (𝓡 3) (𝓡 N) e p v)‖ ^ 2 ≤
      inner ℝ v v at hmetric
    rw [real_inner_self_eq_norm_sq] at hmetric
    have hmul : Real.sqrt c *
        ‖(show EuclideanSpace ℝ (Fin N) from mfderiv (𝓡 3) (𝓡 N) e p v)‖ ≤ ‖v‖ := by
      apply (sq_le_sq₀ (by positivity) (norm_nonneg v)).mp
      rw [mul_pow, Real.sq_sqrt hc.le]
      exact hmetric
    rw [norm_tangentSpace_vectorSpace]
    have hh : ‖(show EuclideanSpace ℝ (Fin N) from mfderiv (𝓡 3) (𝓡 N) e p v)‖ ≤
        ‖v‖ / Real.sqrt c :=
      (le_div_iff₀ hroot).mpr (by simpa only [mul_comm] using hmul)
    calc
      _ ≤ ‖v‖ / Real.sqrt c := hh
      _ = (C : ℝ) * ‖v‖ := by
        change ‖v‖ / Real.sqrt c = (Real.sqrt c)⁻¹ * ‖v‖
        rw [div_eq_mul_inv, mul_comm]
  refine ⟨C, hC, fun p q => ?_⟩
  change edist (e p) (e q) ≤ (C : ℝ≥0∞) * Manifold.riemannianEDist (𝓡 3) p q
  rw [Manifold.riemannianEDist]
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  simp only [ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top, le_iInf_iff]
  intro path hpath
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
      (path ∘ projIcc 0 1 zero_le_one) (Icc 0 1) :=
    contMDiffOn_comp_projIcc_iff.mpr hpath
  have hh := m01_edist_image_le_pathELength isOpen_univ
    (he.of_le (by norm_num)).contMDiffOn C
    (fun y _ => M40.mfderiv_enorm_le_vector_target (hnorm y)) hcomp
    (fun _ _ => mem_univ _)
  simpa using hh

theorem m65SpanningDisk_embedded_lipschitz
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (compact : IsCompact (univ : Set M)) {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ) :
    ∃ C : ℝ≥0, LipschitzOnWith C (e ∘ D.map) loopDiskSet := by
  obtain ⟨C, _hC, hbound⟩ := m65Embedding_edist_bound g e he hinj compact
  let K : ℝ≥0 := ⟨D.lipschitz_constant, D.lipschitz_nonnegative⟩
  have hK : ENNReal.ofReal D.lipschitz_constant = (K : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal D.lipschitz_nonnegative
  refine ⟨C * K, fun x hx y hy => ?_⟩
  have hm : (C : ℝ≥0∞) * g.edist (D.map x) (D.map y) ≤
      C * (ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal ‖x - y‖) := by
    gcongr
    exact D.lipschitz_on_disk ⟨x, hx⟩ ⟨y, hy⟩
  have hh := (hbound (D.map x) (D.map y)).trans
    hm
  simpa only [Function.comp_apply, hK, ENNReal.coe_mul, edist_dist, dist_eq_norm,
    mul_assoc] using hh

end PoincareConjecture
