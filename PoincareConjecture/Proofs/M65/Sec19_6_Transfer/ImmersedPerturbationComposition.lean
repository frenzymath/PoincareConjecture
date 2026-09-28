import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationControls
import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

variable {M : Type u} {n : ℕ}

def foldControls (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) :
    List (Fin n) → (Fin n → ℝ) → ℝ → M → M
  | [], _, _, y => y
  | i :: L, p, x, y => Phi i (foldControls Phi beta L p x y, beta i x * p i)

theorem foldControls_eq_of_zero
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ)
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (L : List (Fin n)) (p : Fin n → ℝ) (x : ℝ) (y : M)
    (hp : ∀ i ∈ L, p i = 0) : foldControls Phi beta L p x y = y := by
  revert hp
  induction L with
  | nil => intro _; rfl
  | cons i L ih =>
    intro hp
    rw [foldControls, ih (fun j hj => hp j (List.mem_cons_of_mem i hj)),
      hp i (List.mem_cons_self), mul_zero, hzero]

theorem foldControls_single
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ)
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (L : List (Fin n)) (hL : L.Nodup) (j : Fin n) (hj : j ∈ L)
    (r x : ℝ) (y : M) :
    foldControls Phi beta L (Pi.single j r) x y = Phi j (y, beta j x * r) := by
  revert hL hj
  induction L with
  | nil => simp
  | cons i L ih =>
    intro hL hj
    obtain ⟨hiL, hL⟩ := List.nodup_cons.mp hL
    by_cases hij : i = j
    · subst i
      have hrest : ∀ k ∈ L, (Pi.single j r : Fin n → ℝ) k = 0 := by
        intro k hk
        have hkj : k ≠ j := fun h => hiL (h ▸ hk)
        simp [hkj]
      rw [foldControls, foldControls_eq_of_zero Phi beta hzero L _ x y hrest]
      simp
    · have hjL : j ∈ L := (List.mem_cons.mp hj).resolve_left (Ne.symm hij)
      rw [foldControls, ih hL hjL]
      have hp : (Pi.single j r : Fin n → ℝ) i = 0 := by
        simp [hij]
      rw [hp, mul_zero, hzero]

theorem foldControls_periodic
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ)
    (hbeta : ∀ i, Function.Periodic (beta i) curvePeriod)
    (L : List (Fin n)) (p : Fin n → ℝ) (y : M) :
    Function.Periodic (fun x => foldControls Phi beta L p x y) curvePeriod := by
  intro x
  induction L with
  | nil => rfl
  | cons i L ih => simp only [foldControls, ih, hbeta i x]

variable [TopologicalSpace M] [ChartedSpace LoopAmbient M]

set_option maxHeartbeats 600000 in

theorem foldControls_contMDiffOn
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i x, |beta i x| ≤ 1) (L : List (Fin n)) :
    ContMDiffOn ((𝓘(ℝ, Fin n → ℝ)).prod ((𝓘(ℝ, ℝ)).prod (𝓡 3))) (𝓡 3) ∞
      (fun z : (Fin n → ℝ) × (ℝ × M) => foldControls Phi beta L z.1 z.2.1 z.2.2)
      (ball 0 d ×ˢ univ) := by
  induction L with
  | nil => exact contMDiff_snd.snd.contMDiffOn
  | cons i L ih =>
    have hweight : ContMDiff ((𝓘(ℝ, Fin n → ℝ)).prod ((𝓘(ℝ, ℝ)).prod (𝓡 3)))
        𝓘(ℝ, ℝ) ∞ (fun z : (Fin n → ℝ) × (ℝ × M) => beta i z.2.1 * z.1 i) :=
      ((hbeta i).contMDiff.comp contMDiff_snd.fst).mul
        ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contMDiff.comp
          contMDiff_fst)
    have hmap : MapsTo (fun z : (Fin n → ℝ) × (ℝ × M) =>
        (foldControls Phi beta L z.1 z.2.1 z.2.2, beta i z.2.1 * z.1 i))
        (ball 0 d ×ˢ univ) (univ ×ˢ Ioo (-d) d) := by
      intro z hz
      refine ⟨mem_univ _, ?_⟩
      have hp : ‖z.1‖ < d := by simpa only [mem_ball, dist_zero_right] using hz.1
      have hnorm : |beta i z.2.1 * z.1 i| < d := by
        calc
          |beta i z.2.1 * z.1 i| = |beta i z.2.1| * |z.1 i| := abs_mul _ _
          _ ≤ 1 * |z.1 i| := mul_le_mul_of_nonneg_right (hbound i z.2.1) (abs_nonneg _)
          _ ≤ ‖z.1‖ := by simpa only [one_mul, Real.norm_eq_abs] using norm_le_pi_norm z.1 i
          _ < d := hp
      exact abs_lt.mp hnorm
    exact (hPhi i).comp (ih.prodMk hweight.contMDiffOn) hmap

end PoincareConjecture.M65Perturbation
