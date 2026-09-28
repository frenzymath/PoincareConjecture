import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Reparametrize
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SmoothSphereIsotopicIn

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U S₀ S₁ S₂ : Set M}

theorem symm (h : SmoothSphereIsotopicIn U S₀ S₁) :
    SmoothSphereIsotopicIn U S₁ S₀ := by
  obtain ⟨H, hH, hembed, hzero, hone⟩ := h
  have htime {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨fun z => H (1 - z.1, z.2), ?_, ?_, ?_, ?_⟩
  · exact hH.comp
      ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      (fun z hz => ⟨htime hz.1, mem_univ _⟩)
  · intro t ht
    exact hembed (1 - t) (htime ht)
  · simpa only [sub_zero] using hone
  · simpa only [sub_self] using hzero

theorem trans (h₀₁ : SmoothSphereIsotopicIn U S₀ S₁)
    (h₁₂ : SmoothSphereIsotopicIn U S₁ S₂) :
    SmoothSphereIsotopicIn U S₀ S₂ := by
  classical
  obtain ⟨H₁, hH₁, hembed₁, h₁zero, h₁one⟩ := h₀₁
  obtain ⟨H₂, hH₂, hembed₂, h₂zero, h₂one⟩ := h₁₂
  obtain ⟨e, he⟩ := (hembed₁ 1 (by norm_num)).1.exists_reparametrizing_diffeomorph
    (hembed₂ 0 (by norm_num)).1 (h₁one.trans h₂zero.symm)
  let L : ℝ × UnitTwoSphere → M :=
    fun z => H₁ (Real.smoothTransition (4 * z.1), z.2)
  let R : ℝ × UnitTwoSphere → M :=
    fun z => H₂ (Real.smoothTransition (4 * z.1 - 3), e z.2)
  have hLsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ L :=
    hH₁.comp_contMDiff
      ((Real.smoothTransition.contDiff.contMDiff.comp
        (contMDiff_const.mul contMDiff_fst)).prodMk contMDiff_snd)
      (fun _ => ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
        mem_univ _⟩)
  have hRsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ R :=
    hH₂.comp_contMDiff
      ((Real.smoothTransition.contDiff.contMDiff.comp
        ((contMDiff_const.mul contMDiff_fst).sub contMDiff_const)).prodMk
        (e.contMDiff.comp contMDiff_snd))
      (fun _ => ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
        mem_univ _⟩)
  have hLembed (t : ℝ) :
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => L (t, q)) ∧
        range (fun q => L (t, q)) ⊆ U :=
    hembed₁ (Real.smoothTransition (4 * t))
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hRembed (t : ℝ) :
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => R (t, q)) ∧
        range (fun q => R (t, q)) ⊆ U := by
    have h := hembed₂ (Real.smoothTransition (4 * t - 3))
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    refine ⟨h.1.comp_diffeomorph e, ?_⟩
    rintro x ⟨q, rfl⟩
    exact h.2 ⟨e q, rfl⟩
  have hoverlap (z : ℝ × UnitTwoSphere) (hlo : 1 / 4 < z.1) (hhi : z.1 < 3 / 4) :
      L z = R z := by
    dsimp [L, R]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    exact (he z.2).symm
  let P : ℝ × UnitTwoSphere → M :=
    fun z => if z.1 ≤ 1 / 2 then L z else R z
  have hlocal (z : ℝ × UnitTwoSphere) :
      (P =ᶠ[𝓝 z] L) ∨ (P =ᶠ[𝓝 z] R) := by
    by_cases hz : z.1 < 3 / 4
    · left
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
      dsimp only [P]
      split_ifs with hhalf
      · rfl
      · exact (hoverlap w (by linarith) hw).symm
    · right
      have hzhalf : 1 / 2 < z.1 := by linarith
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hzhalf] with w hw
      exact if_neg (not_le_of_gt hw)
  have hPsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ P := by
    intro z
    rcases hlocal z with h | h
    · exact hLsmooth.contMDiffAt.congr_of_eventuallyEq h
    · exact hRsmooth.contMDiffAt.congr_of_eventuallyEq h
  refine ⟨P, hPsmooth.contMDiffOn, ?_, ?_, ?_⟩
  · intro t _
    by_cases ht : t ≤ 1 / 2
    · simpa only [P, if_pos ht] using hLembed t
    · simpa only [P, if_neg ht] using hRembed t
  · have heq : (fun q => P (0, q)) = fun q => H₁ (0, q) := by
      funext q
      change (if (0 : ℝ) ≤ 1 / 2 then L (0, q) else R (0, q)) = _
      rw [if_pos (by norm_num)]
      change H₁ (Real.smoothTransition (4 * 0), q) = _
      rw [mul_zero, Real.smoothTransition.zero]
    rw [heq]
    exact h₁zero
  · have heq : (fun q => P (1, q)) = fun q => H₂ (1, e q) := by
      funext q
      change (if (1 : ℝ) ≤ 1 / 2 then L (1, q) else R (1, q)) = _
      rw [if_neg (by norm_num)]
      change H₂ (Real.smoothTransition (4 * 1 - 3), e q) = _
      rw [show (4 : ℝ) * 1 - 3 = 1 by norm_num, Real.smoothTransition.one]
    rw [heq]
    apply Eq.trans _ h₂one
    ext x
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨e q, hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨e.symm q, by simpa only [e.apply_symm_apply] using hq⟩

end PoincareConjecture.SmoothSphereIsotopicIn
