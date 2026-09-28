import PoincareConjecture.Proofs.M35.RawFlow.SectionalRayleigh
import PoincareConjecture.Proofs.M35.RawFlow.SectionalBarrierVelocity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open M04

theorem raw_sectional_velocity_at_distance_minimum {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {s c : ℝ} (hs : s ∈ Ico 0 G.lifetime) (hc : 0 < c)
    {S : Set StandardCapSpace} (y : StandardCapSpace × StandardSectionalPair)
    (hyS : y.1 ∈ interior S) {ψ : StandardCapSpace → ℝ}
    (hψsmooth : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ y.1)
    (hψtouch : ψ y.1 = rawDistanceSquare G 0 s y.1)
    (hψspace : ∀ᶠ a in 𝓝 y.1, rawDistanceSquare G 0 s a ≤ ψ a)
    (hmin : ∀ z : StandardCapSpace × StandardSectionalPair, z.1 ∈ S →
      rawSectionalRayleigh G s y + c * rawDistanceSquare G 0 s y.1 ≤
        rawSectionalRayleigh G s z + c * rawDistanceSquare G 0 s z.1) :
    ∃ vq : ℝ, HasDerivWithinAt (fun t => rawSectionalRayleigh G t y)
        vq (Ico 0 G.lifetime) s ∧
      -(c * (G.flow.connection s).laplacian ψ y.1) + rawSectionalRayleigh G s y *
        ((G.flow.connection s).scalarCurvature y.1 - 2 * rawSectionalRayleigh G s y) ≤ vq := by
  let q := rawSectionalRayleigh G
  let μ := rawDistanceSquare G (0 : StandardCapSpace) s
  let w := q s y + c * μ y.1
  let f : StandardCapSpace → ℝ := fun a => -w + c * ψ a
  have hf : ContDiffAt ℝ ∞ f y.1 :=
    contDiffAt_const.add (contDiffAt_const.mul (contMDiffAt_iff_contDiffAt.mp hψsmooth))
  have hpos : ∀ᶠ a in 𝓝 y.1, ∀ u v : StandardCapSpace,
      0 ≤ (G.flow.connection s).curvatureTensor a u v u v +
        f a * metricGram (G.flow.metric s) a u v := by
    filter_upwards [hψspace, isOpen_interior.mem_nhds hyS] with a ha haS u v
    have hlow (p : StandardCapSpace × StandardCapSpace) (hp : p ∈ modelOrthonormalPairs 3) :
        w - c * ψ a ≤ (G.flow.connection s).sectionalCurvature a p.1 p.2 := by
      have hm := hmin (a, ⟨p, hp⟩) (interior_subset haS)
      have hu := mul_le_mul_of_nonneg_left ha hc.le
      change w ≤ (G.flow.connection s).sectionalCurvature a p.1 p.2 + c * μ a at hm
      change c * μ a ≤ c * ψ a at hu
      linarith
    have hh := sectional_lower_of_modelPairs (G.flow.connection s) a (w - c * ψ a) hlow u v
    dsimp only [f]
    nlinarith only [hh]
  have hgram := metricGram_pos_of_modelPair (G.flow.metric s) y.1 y.2.property
  have hR : q s y * metricGram (G.flow.metric s) y.1 y.2.val.1 y.2.val.2 =
      (G.flow.connection s).curvatureTensor y.1 y.2.val.1 y.2.val.2 y.2.val.1 y.2.val.2 :=
    div_mul_cancel₀ _ hgram.ne'
  have hnull : (G.flow.connection s).curvatureTensor y.1
      y.2.val.1 y.2.val.2 y.2.val.1 y.2.val.2 +
      f y.1 * metricGram (G.flow.metric s) y.1 y.2.val.1 y.2.val.2 = 0 := by
    dsimp only [f]
    rw [hψtouch]
    change _ + (-(q s y + c * μ y.1) + c * μ y.1) * _ = 0
    nlinarith only [hR]
  obtain ⟨vq, hdq, hqheat⟩ := sectional_velocity_lower_bound_at_barrier_contact G.flow
    hs y.2.property hf hpos hnull
  have hflap : (G.flow.connection s).laplacian f y.1 =
      c * (G.flow.connection s).laplacian ψ y.1 := by
    have hcs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun a => c * ψ a) y.1 :=
      contMDiffAt_const.mul hψsmooth
    rw [show f = fun a => -w + c * ψ a from rfl,
      laplacian_const_add_at _ hcs (-w),
      LeviCivitaData.laplacian_const_mul]
  rw [hflap] at hqheat
  exact ⟨vq, hdq, hqheat⟩

end PoincareConjecture.M35.Uniqueness
