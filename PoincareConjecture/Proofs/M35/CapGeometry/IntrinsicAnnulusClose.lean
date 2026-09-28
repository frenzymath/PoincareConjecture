import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicAnnulusJets
import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem intrinsic_annulus_eventually_close
    (g : ℕ → RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (g k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (g k).inner x u v)
    (hcomplete : ∀ k, MetricComplete (g k)) (a b : ℕ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hb : Tendsto b atTop (𝓝 1))
    (hjet : ∀ (idx : ℕ → ℕ), Tendsto idx atTop atTop →
      ∀ (s : ℕ → ℝ), (∀ k, s k ∈ Icc (-epsilon⁻¹) epsilon⁻¹) → ∀ m : ℕ,
        Tendsto (fun k => iteratedDeriv m
          (fun r => intrinsicWarpingRadius (g (idx k)) (hrotation (idx k))
            (hcomplete (idx k)) r ^ 2) (a (idx k) + b (idx k) * s k))
          atTop (𝓝 (if m = 0 then 2 else 0))) :
    ∀ᶠ k in atTop, RoundCylinderClose epsilon 0
      (radialCylinderTensor
        (fun u => intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k)
          (a k + b k * u) ^ 2) (b k)) := by
  let B (k : ℕ) := radialCylinderTensor
    (fun u => intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k)
      (a k + b k * u) ^ 2) (b k)
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hseq : ∀ (idx : ℕ → ℕ), Tendsto idx atTop atTop →
      ∀ (z : ℕ → RoundCylinderSpace), (∀ k, z k ∈ K) →
      ∀ z₀ ∈ K, Tendsto z atTop (𝓝 z₀) →
        Tendsto (fun k => roundCylinderJetErrorSquared 0 (B (idx k))
          ⌊epsilon⁻¹⌋₊ (z k)) atTop (𝓝 0) := by
    intro idx hidx z hz z₀ _hz₀ hlim
    exact intrinsic_annulus_jetError_tendsto_zero
      (fun k => g (idx k)) (fun k => hrotation (idx k)) (fun k => hcomplete (idx k))
      (a ∘ idx) (b ∘ idx) (fun k => (z k).2) z₀.2 (fun k => (z k).1)
      ⌊epsilon⁻¹⌋₊ (hb.comp hidx) (continuous_snd.tendsto z₀ |>.comp hlim)
      (hjet idx hidx (fun k => (z k).2) (fun k => (hz k).2))
  obtain ⟨n, hn⟩ := OrdinaryRealization.uniform_of_moving_point_limits
    (F := fun k z => roundCylinderJetErrorSquared 0 (B k) ⌊epsilon⁻¹⌋₊ z)
    (G := fun _ => 0) hK continuousOn_const hseq
    (by positivity : 0 < epsilon ^ 2 / 2)
  filter_upwards [eventually_ge_atTop n] with k hk
  refine ⟨?_, epsilon ^ 2 / 2, by nlinarith only [sq_pos_of_pos hepsilon], ?_⟩
  · intro q i j p _hp
    apply (radialCylinderTensor_coefficient_contDiffAt (b k) q ?_ i j).contDiffWithinAt
    exact (((intrinsicWarpingRadius_contDiff (g k) (hrotation k) (hcomplete k)).pow 2).comp
      (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffAt
  · intro z hz
    have h := hn k hk z ⟨mem_univ _, ⟨hz.1.le, hz.2.le⟩⟩
    rw [sub_zero] at h
    exact le_of_lt ((le_abs_self _).trans_lt h)

end PoincareConjecture.M35.Uniqueness
