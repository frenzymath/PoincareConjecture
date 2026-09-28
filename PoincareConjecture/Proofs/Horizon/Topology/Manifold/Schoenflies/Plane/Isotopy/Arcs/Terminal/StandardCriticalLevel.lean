import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.CriticalPoints
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

theorem standard_critical_level_preconnected :
    IsPreconnected {q : S2 | Saddle.height q = -1} := by
  have hnorm (q : S1) : (q : E2) 0 ^ 2 + (q : E2) 1 ^ 2 = 1 := by
    rw [← Saddle.norm_sq_two, norm_eq_of_mem_sphere q]
    norm_num
  have hrad (q : S1) : 0 ≤ (1 + (q : E2) 1) / 2 := by
    have h := hnorm q
    nlinarith [sq_nonneg ((q : E2) 0)]
  let v (σ : Real) (q : S1) : E3 := WithLp.toLp 2
    ![σ * Real.sqrt ((1 + (q : E2) 1) / 2), (q : E2) 0 / 2, ((q : E2) 1 - 1) / 2]
  have hv (σ : Real) (hσ : σ ^ 2 = 1) (q : S1) : ‖v σ q‖ = 1 := by
    have hn := EuclideanSpace.norm_sq_eq (v σ q)
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    change ‖v σ q‖ ^ 2 = (σ * Real.sqrt ((1 + (q : E2) 1) / 2)) ^ 2 +
      ((q : E2) 0 / 2) ^ 2 + (((q : E2) 1 - 1) / 2) ^ 2 at hn
    rw [mul_pow, hσ, one_mul, Real.sq_sqrt (hrad q)] at hn
    nlinarith [hnorm q, norm_nonneg (v σ q)]
  let γ (σ : Real) (hσ : σ ^ 2 = 1) (q : S1) : S2 :=
    ⟨v σ q, mem_sphere_zero_iff_norm.mpr (hv σ hσ q)⟩
  have hγ (σ : Real) (hσ : σ ^ 2 = 1) : Continuous (γ σ hσ) := by
    apply Continuous.subtype_mk
    dsimp [v]
    fun_prop
  have hheight (σ : Real) (hσ : σ ^ 2 = 1) (q : S1) : Saddle.height (γ σ hσ q) = -1 := by
    rw [Saddle.height_apply]
    change ((q : E2) 1 - 1) / 2 - (σ * Real.sqrt ((1 + (q : E2) 1) / 2)) ^ 2 = -1
    rw [mul_pow, hσ, one_mul, Real.sq_sqrt (hrad q)]
    ring
  let q₀ : S1 := ⟨-EuclideanSpace.single 1 1, by simp⟩
  have hbase (σ : Real) (hσ : σ ^ 2 = 1) : γ σ hσ q₀ = Saddle.saddlePoint := by
    apply Subtype.ext
    ext i
    fin_cases i <;> norm_num [γ, v, q₀, Saddle.saddlePoint] <;> decide
  have hcover : range (γ 1 (by norm_num)) ∪ range (γ (-1) (by norm_num)) =
      {q : S2 | Saddle.height q = -1} := by
    apply Subset.antisymm
    · rintro q (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact hheight 1 (by norm_num) u
      · exact hheight (-1) (by norm_num) u
    · intro q hq
      change Saddle.height q = -1 at hq
      rw [Saddle.height_apply] at hq
      have hqn := EuclideanSpace.norm_sq_eq (q : E3)
      rw [norm_eq_of_mem_sphere q] at hqn
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hqn
      let u : E2 := WithLp.toLp 2 ![2 * (q : E3) 1, 2 * (q : E3) 2 + 1]
      have hu : ‖u‖ = 1 := by
        have hn := Saddle.norm_sq_two u
        change ‖u‖ ^ 2 = (2 * (q : E3) 1) ^ 2 + (2 * (q : E3) 2 + 1) ^ 2 at hn
        nlinarith [norm_nonneg u]
      let u' : S1 := ⟨u, mem_sphere_zero_iff_norm.mpr hu⟩
      have hradq : (1 + (u' : E2) 1) / 2 = (q : E3) 0 ^ 2 := by
        change (1 + (2 * (q : E3) 2 + 1)) / 2 = _
        linarith
      have heq (σ : Real) (hσ : σ ^ 2 = 1) (hs : σ * |(q : E3) 0| = (q : E3) 0) :
          γ σ hσ u' = q := by
        apply Subtype.ext
        ext i
        fin_cases i
        · change σ * Real.sqrt ((1 + (u' : E2) 1) / 2) = (q : E3) 0
          rw [hradq, Real.sqrt_sq_eq_abs, hs]
        · change (2 * (q : E3) 1) / 2 = (q : E3) 1
          ring
        · change (2 * (q : E3) 2 + 1 - 1) / 2 = (q : E3) 2
          ring
      by_cases hx : 0 ≤ (q : E3) 0
      · exact Or.inl ⟨u', heq 1 (by norm_num) (by simp [abs_of_nonneg hx])⟩
      · exact Or.inr ⟨u', heq (-1) (by norm_num) (by simp [abs_of_neg (lt_of_not_ge hx)])⟩
  rw [← hcover]
  apply IsPreconnected.union Saddle.saddlePoint
  · exact ⟨q₀, hbase 1 (by norm_num)⟩
  · exact ⟨q₀, hbase (-1) (by norm_num)⟩
  · exact isPreconnected_range (hγ 1 (by norm_num))
  · exact isPreconnected_range (hγ (-1) (by norm_num))

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
