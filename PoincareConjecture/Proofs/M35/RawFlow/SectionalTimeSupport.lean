import PoincareConjecture.Proofs.M35.RawFlow.SectionalDistanceSupport








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem raw_sectional_barrier_time_support {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {s K C ε : ℝ}
    (hs : s ∈ Ico 0 G.lifetime) (hε : 0 < ε)
    (hnorm : ∀ x, (G.flow.connection s).curvatureTensorNorm x ≤ K)
    {S : Set StandardCapSpace} (y : StandardCapSpace × StandardSectionalPair)
    (hyS : y.1 ∈ interior S)
    (hsupp : ∀ η > 0, ∃ ψ : ℝ → StandardCapSpace → ℝ, ∃ v : ℝ,
      ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (ψ s) y.1 ∧
      ψ s y.1 = rawDistanceSquare G 0 s y.1 ∧
      (∀ᶠ a in 𝓝 y.1, rawDistanceSquare G 0 s a ≤ ψ s a) ∧
      (∀ r ∈ Icc 0 s, rawDistanceSquare G 0 r y.1 ≤ ψ r y.1) ∧
      HasDerivAt (fun r => ψ r y.1) v s ∧
      -C * rawDistanceSquare G 0 s y.1 - η ≤
        v - (G.flow.connection s).laplacian (ψ s) y.1) :
    let w := fun r (z : StandardCapSpace × StandardSectionalPair) =>
      rawSectionalRayleigh G r z +
        ε * Real.exp ((C + 11 * K) * r) * rawDistanceSquare G 0 r z.1
    (∀ z : StandardCapSpace × StandardSectionalPair, z.1 ∈ S → w s y ≤ w s z) →
    w s y < 0 → ∀ δ > 0, ∃ χ : ℝ → ℝ, ∃ v : ℝ,
      χ s = w s y ∧ (∀ᶠ r in 𝓝[Icc 0 s] s, w r y ≤ χ r) ∧
      HasDerivWithinAt χ v (Icc 0 s) s ∧ -(-(11 * K)) * w s y - δ ≤ v := by
  intro w hmin hneg δ hδ
  let q := rawSectionalRayleigh G
  let μ := rawDistanceSquare G (0 : StandardCapSpace)
  let L := 11 * K
  let A := C + L
  let c := ε * Real.exp (A * s)
  have hc : 0 < c := mul_pos hε (Real.exp_pos _)
  have hμ : 0 < μ s y.1 := by dsimp [μ, rawDistanceSquare]; positivity
  obtain ⟨ψ, vμ, hψsmooth, hψtouch, hψspace, hψtime, hψderiv, hψheat⟩ :=
    hsupp (δ / c) (by positivity)
  obtain ⟨vq, hdq, hqheat⟩ := raw_sectional_velocity_at_distance_minimum G
    hs hc y hyS hψsmooth hψtouch hψspace hmin
  have hqneg : q s y < 0 := by
    change q s y + c * μ s y.1 < 0 at hneg
    have hprod := mul_pos hc hμ
    linarith
  have hrate := rawSectionalRayleigh_reaction_bound G hnorm y
  have hqvelocity : L * q s y ≤ vq + c * (G.flow.connection s).laplacian (ψ s) y.1 := by
    have hh := mul_le_mul_of_nonpos_left hrate hqneg.le
    change -(c * (G.flow.connection s).laplacian (ψ s) y.1) +
      q s y * ((G.flow.connection s).scalarCurvature y.1 - 2 * q s y) ≤ vq at hqheat
    dsimp only [L]
    nlinarith only [hh, hqheat]
  let χ : ℝ → ℝ := fun r => q r y + ε * Real.exp (A * r) * ψ r y.1
  have htouch : χ s = w s y := by dsimp [χ, w]; rw [hψtouch]
  have htime : ∀ᶠ r in 𝓝[Icc 0 s] s, w r y ≤ χ r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hψtime r hr) (by positivity))
  have hederiv : HasDerivAt (fun r => ε * Real.exp (A * r)) (c * A) s := by
    convert! (((hasDerivAt_id s).const_mul A).exp.const_mul ε) using 1
    dsimp only [c, id_eq]
    ring
  have hderiv : HasDerivWithinAt χ (vq + c * (A * ψ s y.1 + vμ)) (Icc 0 s) s := by
    convert! (hdq.mono (show Icc 0 s ⊆ Ico 0 G.lifetime from
      fun r hr => ⟨hr.1, hr.2.trans_lt hs.2⟩)).add
      (hederiv.mul hψderiv).hasDerivWithinAt using 1
    ring
  refine ⟨χ, vq + c * (A * ψ s y.1 + vμ), htouch, htime, hderiv, ?_⟩
  have hδeq : c * (δ / c) = δ := mul_div_cancel₀ δ hc.ne'
  have hscaled := mul_le_mul_of_nonneg_left hψheat hc.le
  rw [mul_sub, hδeq] at hscaled
  rw [hψtouch]
  change -(-L) * (q s y + c * μ s y.1) - δ ≤ vq + c * (A * μ s y.1 + vμ)
  change c * (-C * μ s y.1) - δ ≤
    c * (vμ - (G.flow.connection s).laplacian (ψ s) y.1) at hscaled
  dsimp only [A]
  nlinarith only [hqvelocity, hscaled]

end PoincareConjecture.M35.Uniqueness
