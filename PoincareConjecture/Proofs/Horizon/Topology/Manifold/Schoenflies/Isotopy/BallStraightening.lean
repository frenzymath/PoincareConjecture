import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.ChartShrinking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.ChartLinearization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E A H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}

theorem exists_supported_ball_straightening
    (e d : OpenPartialHomeomorph E M)
    (he : ContMDiffOn 𝓘(Real, E) I ∞ e e.source)
    (hei : ContMDiffOn I 𝓘(Real, E) ∞ e.symm e.target)
    (hd : ContMDiffOn 𝓘(Real, E) I ∞ d d.source)
    (hdi : ContMDiffOn I 𝓘(Real, E) ∞ d.symm d.target)
    {r : Real} (hr : 0 < r) (hball : closedBall (0 : E) r ⊆ e.source)
    (hd0 : (0 : E) ∈ d.source) (hcenter : e 0 = d 0) :
    ∃ L : E ≃L[Real] E, MapsTo L (closedBall (0 : E) r) d.source ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ e.target ∪ d.target ∧
      ∃ Phi : Real -> Diffeomorph I I M M ∞,
      (∀ x, Phi 0 x = x) ∧
      ContMDiff (𝓘(Real, Real).prod I) I ∞ (fun p : Real × M => Phi p.1 p.2) ∧
      (∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ x ∈ closedBall (0 : E) r, Phi 1 (e x) = d (L x) := by
  have he0 : (0 : E) ∈ e.source := hball (mem_closedBall_self hr.le)
  obtain ⟨rho, hrho, B, KQ, hKQ, hKQd, Q, hQ0, hQs, hQfix, hBd, hQ⟩ :=
    exists_supported_chart_linearization e d he hei hd hdi he0 hd0 hcenter
  let c := min 1 (rho / r)
  have hc : 0 < c := lt_min zero_lt_one (div_pos hrho hr)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcr : c * r ≤ rho := (le_div_iff₀ hr).mp (min_le_right _ _)
  have hcx (x : E) (hx : x ∈ closedBall (0 : E) r) : c • x ∈ closedBall (0 : E) rho := by
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left hx hc.le).trans hcr
  obtain ⟨KP, hKP, hKPe, P, hP0, hPs, hPfix, hP⟩ :=
    exists_supported_chart_shrinking_isotopy e he hei hr hc hc1 hball
  let C : E ≃L[Real] E := (LinearEquiv.smulOfNeZero Real E c hc.ne').toContinuousLinearEquiv
  let L := C.trans B
  let Phi : Real -> Diffeomorph I I M M ∞ := fun t => (P t).trans (Q t)
  refine ⟨L, (fun x hx => hBd (hcx x hx)), KP ∪ KQ, hKP.union hKQ,
    union_subset_union hKPe hKQd, Phi, ?_, ?_, ?_, ?_⟩
  · intro x
    change Q 0 (P 0 x) = x
    rw [hP0, hQ0]
  · exact hQs.comp (contMDiff_fst.prodMk hPs)
  · intro t x hx
    change Q t (P t x) = x
    rw [hPfix t x (fun h => hx (Or.inl h)), hQfix t x (fun h => hx (Or.inr h))]
  · intro x hx
    change Q 1 (P 1 (e x)) = d (B (c • x))
    have hP1 : P 1 (e x) = e (c • x) := by
      simpa only [one_mul, Real.exp_log hc] using
        hP 1 (show (1 : Real) ∈ Icc 0 1 by simp) x hx
    rw [hP1, hQ _ (hcx x hx)]

end Poincare.Manifold.Schoenflies
