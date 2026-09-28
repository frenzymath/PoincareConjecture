import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ContinuousOperator
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.Kernel.ContinuousRows







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

private theorem evaluationRow_zero_outside (k : ℕ) (t : ℝ) (ht : 0 < t)
    (x : M) (hx : x ∉ Ω) :
    evaluationRow (heatPowerContinuous D S k t ht) x = 0 := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationRow, inner_zero_left]
  exact heatPowerContinuous_zero_outside D S k t ht f x hx

private theorem evaluationRow_add (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : M) :
    evaluationRow (heatPowerContinuous D S 0 (s + t) (add_pos hs ht)) x =
      heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure
        t.toNNReal (evaluationRow (heatPowerContinuous D S 0 s hs) x) := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationRow, heatPowerContinuous_add_comp D S 0 s t hs ht]
  rw [(heatSemigroup_isSelfAdjoint D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure t.toNNReal).isSymmetric.apply_clm]
  exact (inner_evaluationRow (heatPowerContinuous D S 0 s hs) x _).symm


def heatKernelContinuous (t : ℝ) (ht : 0 < t) (x y : M) : ℝ :=
  inner ℝ (evaluationRow (heatPowerContinuous D S 0 (t / 2) (half_pos ht)) x)
    (evaluationRow (heatPowerContinuous D S 0 (t / 2) (half_pos ht)) y)

theorem continuous_heatKernelContinuous (t : ℝ) (ht : 0 < t) :
    Continuous (fun p : M × M => heatKernelContinuous D S t ht p.1 p.2) := by
  have h := continuous_evaluationRow (heatPowerContinuous D S 0 (t / 2) (half_pos ht))
    (isCompactOperator_heatPowerContinuous D S 0 (t / 2) (half_pos ht))
  exact (h.comp continuous_fst).inner (h.comp continuous_snd)

theorem heatKernelContinuous_symm (t : ℝ) (ht : 0 < t) (x y : M) :
    heatKernelContinuous D S t ht x y = heatKernelContinuous D S t ht y x :=
  real_inner_comm _ _

theorem heatKernelContinuous_zero (t : ℝ) (ht : 0 < t) (x y : M)
    (h : x ∉ Ω ∨ y ∉ Ω) : heatKernelContinuous D S t ht x y = 0 := by
  rcases h with hx | hy
  · rw [heatKernelContinuous, evaluationRow_zero_outside D S 0 _ _ x hx, inner_zero_left]
  · rw [heatKernelContinuous, evaluationRow_zero_outside D S 0 _ _ y hy, inner_zero_right]

theorem heatKernelContinuous_eq_heatPowerContinuous (t : ℝ) (ht : 0 < t) (x y : M) :
    heatKernelContinuous D S t ht x y = heatPowerContinuous D S 0 (t / 2) (half_pos ht)
      (evaluationRow (heatPowerContinuous D S 0 (t / 2) (half_pos ht)) y) x :=
  inner_evaluationRow _ _ _

theorem contMDiffOn_heatKernelContinuous_left (t : ℝ) (ht : 0 < t) (y : M) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => heatKernelContinuous D S t ht x y) Ω := by
  simp_rw [heatKernelContinuous_eq_heatPowerContinuous]
  exact contMDiffOn_heatPowerContinuous D S 0 (t / 2) (half_pos ht) _

theorem contMDiffOn_heatKernelContinuous_right (t : ℝ) (ht : 0 < t) (x : M) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (heatKernelContinuous D S t ht x) Ω := by
  have h : heatKernelContinuous D S t ht x = fun y => heatKernelContinuous D S t ht y x :=
    funext fun y => heatKernelContinuous_symm D S t ht x y
  rw [h]
  exact contMDiffOn_heatKernelContinuous_left D S t ht x

theorem heatKernelContinuous_row_ae (t : ℝ) (ht : 0 < t) (x : M) :
    heatKernelContinuous D S t ht x =ᵐ[g.volumeMeasure.restrict Ω]
      (evaluationRow (E := Lp ℝ 2 (g.volumeMeasure.restrict Ω))
        (heatPowerContinuous D S 0 t ht) x : M → ℝ) := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hfac := evaluationRow_add D S (t / 2) (t / 2) hhalf hhalf x
  simp only [add_halves] at hfac
  have hae := heatPowerContinuous_ae D S 0 (t / 2) hhalf
    (evaluationRow (heatPowerContinuous D S 0 (t / 2) hhalf) x)
  rw [heatSpectralPower_zero_eq_heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure hhalf, ← hfac] at hae
  filter_upwards [hae] with y hy
  rw [heatKernelContinuous_symm D S t ht x y,
    heatKernelContinuous_eq_heatPowerContinuous]
  exact hy

theorem integrable_heatKernelContinuous_mul (t : ℝ) (ht : 0 < t)
    (x : M) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    Integrable (fun y => heatKernelContinuous D S t ht x y * f y)
      (g.volumeMeasure.restrict Ω) := by
  have h := L2.integrable_inner (𝕜 := ℝ)
    (evaluationRow (heatPowerContinuous D S 0 t ht) x) f
  apply h.congr
  filter_upwards [heatKernelContinuous_row_ae D S t ht x] with y hy
  simp [hy, mul_comm]

theorem integral_heatKernelContinuous_mul (t : ℝ) (ht : 0 < t)
    (x : M) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (∫ y, heatKernelContinuous D S t ht x y * f y ∂(g.volumeMeasure.restrict Ω)) =
      heatPowerContinuous D S 0 t ht f x := by
  rw [← inner_evaluationRow (heatPowerContinuous D S 0 t ht) x f, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [heatKernelContinuous_row_ae D S t ht x] with y hy
  simp [hy, mul_comm]


theorem heatKernelContinuous_spec (t : ℝ) (ht : 0 < t) :
    Continuous (fun p : M × M => heatKernelContinuous D S t ht p.1 p.2) ∧
    (∀ x y : M, heatKernelContinuous D S t ht x y = heatKernelContinuous D S t ht y x) ∧
    (∀ x y : M, x ∉ Ω ∨ y ∉ Ω → heatKernelContinuous D S t ht x y = 0) ∧
    (∀ y : M, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => heatKernelContinuous D S t ht x y) Ω) ∧
    (∀ x : M, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (heatKernelContinuous D S t ht x) Ω) ∧
    (∀ (x : M) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)),
      Integrable (fun y => heatKernelContinuous D S t ht x y * f y)
        (g.volumeMeasure.restrict Ω) ∧
      (∫ y, heatKernelContinuous D S t ht x y * f y ∂(g.volumeMeasure.restrict Ω)) =
        heatPowerContinuous D S 0 t ht f x) :=
  ⟨continuous_heatKernelContinuous D S t ht, heatKernelContinuous_symm D S t ht,
    heatKernelContinuous_zero D S t ht, contMDiffOn_heatKernelContinuous_left D S t ht,
    contMDiffOn_heatKernelContinuous_right D S t ht, fun x f =>
      ⟨integrable_heatKernelContinuous_mul D S t ht x f,
        integral_heatKernelContinuous_mul D S t ht x f⟩⟩

end PoincareConjecture.LeviCivitaData.Dirichlet
