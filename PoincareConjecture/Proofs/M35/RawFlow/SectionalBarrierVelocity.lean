import PoincareConjecture.Proofs.M35.RawFlow.SectionalBarrierDiffusion
import PoincareConjecture.Proofs.M35.RawFlow.SectionalPlanes
import PoincareConjecture.Proofs.M04.SectionalNullReaction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open M04

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem sectional_velocity_lower_bound_at_barrier_contact
    {J : Set ℝ} (F : RicciFlow 3 V J) {t : ℝ} (ht : t ∈ J) {x : V}
    {p : V × V} (hp : p ∈ modelOrthonormalPairs 3) {f : V → ℝ}
    (hf : ContDiffAt ℝ ∞ f x)
    (hpos : ∀ᶠ y in 𝓝 x, ∀ a b : V,
      0 ≤ (F.connection t).curvatureTensor y a b a b + f y * metricGram (F.metric t) y a b)
    (hnull : (F.connection t).curvatureTensor x p.1 p.2 p.1 p.2 +
      f x * metricGram (F.metric t) x p.1 p.2 = 0) :
    ∃ v : ℝ, HasDerivWithinAt (fun s => (F.connection s).sectionalCurvature x p.1 p.2) v J t ∧
      -(F.connection t).laplacian f x +
        (F.connection t).sectionalCurvature x p.1 p.2 *
          ((F.connection t).scalarCurvature x -
            2 * (F.connection t).sectionalCurvature x p.1 p.2) ≤ v := by
  let D := F.connection t
  let g := F.metric t
  let R := D.curvatureTensor x p.1 p.2 p.1 p.2
  let H := metricGram g x p.1 p.2
  let m := D.sectionalCurvature x p.1 p.2
  let L := D.tensorLaplacian D.riemannEvaluation x ![p.1, p.2, p.1, p.2]
  let Q := D.curvatureReaction x p.1 p.2 p.1 p.2
  let Vg := -2 * D.ricci x p.1 p.1 * g.inner x p.2 p.2 -
    2 * g.inner x p.1 p.1 * D.ricci x p.2 p.2 +
    4 * D.ricci x p.1 p.2 * g.inner x p.1 p.2
  let v := (L + Q) / H - R * Vg / H ^ 2
  have hH : 0 < H := metricGram_pos_of_modelPair g x hp
  have hR : R = m * H := (div_mul_cancel₀ R hH.ne').symm
  have hfm : f x = -m := by
    apply (mul_right_inj' hH.ne').mp
    change R + f x * H = 0 at hnull
    rw [hR] at hnull
    nlinarith only [hnull]
  refine ⟨v, hasDerivWithinAt_sectionalRayleigh F t ht x p.1 p.2 hH, ?_⟩
  have hlap : 0 ≤ L + D.laplacian f x * H :=
    curvature_diffusion_with_local_scalar_barrier D hf hpos p.1 p.2 hnull
  have hshift : ∀ a b : V,
      0 ≤ D.curvatureTensor x a b a b + (-m) * metricGram g x a b := by
    intro a b
    simpa only [hfm] using hpos.self_of_nhds a b
  have hreact : m * (D.scalarCurvature x - 2 * m) * H ≤ Q - m * Vg := by
    have h := curvatureReaction_lower_bound_of_shiftedSectional_null D x (-m) hshift
      p.1 p.2 (by rw [← hfm]; exact hnull)
    change -(-m) * (D.scalarCurvature x + 2 * (-m)) * H ≤ Q + (-m) * Vg at h
    convert! h using 1 <;> ring
  have hvelocity : v * H = L + Q - m * Vg := by
    dsimp only [v]
    rw [hR]
    field_simp [hH.ne']
  apply (mul_le_mul_iff_left₀ hH).mp
  change (-D.laplacian f x + m * (D.scalarCurvature x - 2 * m)) * H ≤ v * H
  nlinarith only [hlap, hreact, hvelocity]

end PoincareConjecture.M35.Uniqueness
