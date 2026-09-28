import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Field
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Graph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Flow

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_supported_graph_push
    (b : E -> Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b) :
    ∃ R : Real, 0 < R ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p, (F p).1 = p.1) ∧
        (∀ p ∉ tsupport b ×ˢ closedBall (0 : Real) R, F p = p) ∧
        (∀ x, F (x, 0) = (x, b x)) ∧
        F '' {p : E × Real | p.2 ≤ 0} = {p | p.2 ≤ b p.1} := by
  obtain ⟨R, hR, V, hV, hVfirst, hVzero, hVline⟩ :=
    exists_vertical_graph_field b hb hbc
  let K := tsupport b ×ˢ closedBall (0 : Real) R
  have hK : IsCompact K := hbc.prod (isCompact_closedBall 0 R)
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun p : Real × (E × Real) => V p.2) (hV.comp contDiff_snd) hK
      (fun _ p hp => hVzero p hp)
  have hfirst (s t : Real) (p : E × Real) : (Phi s t p).1 = p.1 := by
    have hd (r : Real) : HasDerivAt (fun r => (Phi s r p).1) 0 r := by
      have h := (ContinuousLinearMap.fst Real E Real).hasFDerivAt.comp_hasDerivAt r
        (ho s p r)
      change HasDerivAt (fun r => (Phi s r p).1) (V (Phi s r p)).1 r at h
      rwa [hVfirst] at h
    have he := is_const_of_deriv_eq_zero
      (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t s
    simpa only [hi] using he
  have hVc : HasCompactSupport V := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra hn
    exact hp (hVzero p hn)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hgraph (x : E) : Phi 0 1 (x, 0) = (x, b x) := by
    have hd (t : Real) : HasDerivAt (fun r : Real => (x, r * b x)) (0, b x) t := by
      simpa using (hasDerivAt_const t x).prodMk ((hasDerivAt_id t).mul_const (b x))
    have he := ODE_solution_unique (v := fun _ => V) (fun _ => hL)
      (f := fun t => Phi 0 t (x, 0)) (g := fun t : Real => (x, t * b x))
      ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ => (ho 0 (x, 0) t).hasDerivWithinAt)
      (continuous_const.prodMk (continuous_id.mul continuous_const)).continuousOn
      (fun t ht => by
        rw [hVline x t ⟨ht.1, ht.2.le⟩]
        exact (hd t).hasDerivWithinAt)
      (by simp only [hi, zero_mul])
    simpa only [one_mul] using he (show (1 : Real) ∈ Icc 0 1 by simp)
  refine ⟨R, hR, Phi 0 1, hfirst 0 1, hfix 0 1, hgraph, ?_⟩
  exact image_lowerHalfSpace_eq_subgraph (Phi 0 1).toHomeomorph
    (hfirst 0 1) hK (hfix 0 1) b hgraph

end Poincare.Manifold.Schoenflies
