import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEnergyLimit
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ}

private theorem m65WeakDisk_energy_nonnegative (g : RiemannianMetric 3 M)
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M} (F : M65WeakDisk e γ) :
    0 ≤ F.energy g := by
  apply integral_nonneg
  intro z
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact Finset.sum_nonneg fun i _ => m65EmbeddingMetric_nonneg g e (F.value z) _

private theorem m65WeakDisk_gradient_coercive (g : RiemannianMetric 3 M)
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M} (F : M65WeakDisk e γ)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {c C : ℝ} (hb : ∀ p (v : EuclideanSpace ℝ (Fin N)),
      c * ‖v‖ ^ 2 ≤ m65EmbeddingMetric g e p v v ∧
        m65EmbeddingMetric g e p v v ≤ C * ‖v‖ ^ 2) :
    (c / 2) * (‖F.derivative 0‖ ^ 2 + ‖F.derivative 1‖ ^ 2) ≤ F.energy g := by
  have hi (i : Fin 2) : Integrable (fun z => ‖F.derivative i z‖ ^ 2)
      (volume.restrict loopDiskSet) := (Lp.memLp (F.derivative i)).norm.integrable_sq
  have hbound := integral_mono
    ((integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul (c / 2))
    (F.energy_integrable g he hinj hemb compact)
    (fun z => (m65EmbeddedEnergyDensity_bounds g e hb F.value
      (fun i z => F.derivative i z) z).1)
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i] at hbound
  simp only [← Lp.norm_sq_eq_integral_norm_sq, Fin.sum_univ_two] at hbound
  exact hbound

theorem m65WeakDisk_exists_normalized_minimum (g : RiemannianMetric 3 M)
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hγ : Continuous γ) (hJordan : Function.Injective (e ∘ γ))
    {a b c : LoopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (F0 : M65WeakDisk e γ) (hF0 : F0.Normalized a b c) :
    ∃ G : M65WeakDisk e γ, G.MinimizesNormalizedEnergy g a b c := by
  classical
  let S : Set ℝ := {x | ∃ F : M65WeakDisk e γ, F.Normalized a b c ∧ F.energy g = x}
  have hS : S.Nonempty := ⟨F0.energy g, F0, hF0, rfl⟩
  have hSbound : BddBelow S := ⟨0, by
    rintro x ⟨F, _hF, rfl⟩
    exact m65WeakDisk_energy_nonnegative g F⟩
  obtain ⟨v, hvanti, hvlim, hvmem⟩ := exists_seq_tendsto_sInf hS hSbound
  choose F hpin hFE using hvmem
  have henergy : Tendsto (fun n => (F n).energy g) atTop (𝓝 (sInf S)) := by
    simpa only [hFE] using hvlim
  obtain ⟨k, C, hk, _hC, hmetric⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  let K := 2 * max (v 0) 0 / k
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hv0 : v 0 ≤ k * K / 2 := by
    dsimp only [K]
    have heq : k * (2 * max (v 0) 0 / k) / 2 = max (v 0) 0 := by field_simp
    rw [heq]
    exact le_max_left _ _
  have hd (n : ℕ) (i : Fin 2) : ‖(F n).derivative i‖ ≤ K + 1 := by
    have hc0 := m65WeakDisk_gradient_coercive g (F n) he hinj hemb compact hmetric
    have he0 : (F n).energy g ≤ v 0 := by rw [hFE]; exact hvanti (Nat.zero_le n)
    have hsum : ‖(F n).derivative i‖ ^ 2 ≤
        ‖(F n).derivative 0‖ ^ 2 + ‖(F n).derivative 1‖ ^ 2 := by
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · exact le_add_of_nonneg_left (sq_nonneg _)
    have hiK : ‖(F n).derivative i‖ ^ 2 ≤ K := by nlinarith
    nlinarith [norm_nonneg ((F n).derivative i)]
  obtain ⟨σ, G, hσ, hG, hstrong, hweak, _hboundary⟩ :=
    m65NormalizedWeakDisks_subsequence F compact he.continuous hγ hJordan hab hac hbc hpin
      (by positivity : 0 ≤ K + 1) hd
  have hmin : G.energy g ≤ sInf S := m65WeakDisk_energy_le_of_limit g he hinj hemb compact
    (fun n => F (σ n)) G hstrong (fun n i => hd (σ n) i) hweak
    (henergy.comp hσ.tendsto_atTop)
  refine ⟨G, hG, fun Q hQ => hmin.trans ?_⟩
  exact csInf_le hSbound ⟨Q, hQ, rfl⟩

end PoincareConjecture
