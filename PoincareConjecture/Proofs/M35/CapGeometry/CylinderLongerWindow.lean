import PoincareConjecture.Proofs.M35.CapGeometry.CylinderTimeEstimate
import PoincareConjecture.Proofs.M35.Thm12_28.NeckRestriction









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RoundCylinderFamilyClose




theorem extend_affine_window {delta epsilon : ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (h : RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0) B)
    (hd : 0 < delta) (hde : delta ≤ epsilon) (eta : ℝ) (heta : eta ≤ 1)
    (hsmall : ((⌊epsilon⁻¹⌋₊ + 1 : ℕ) : ℝ) *
      (18 + 32 * 2 ^ (⌊epsilon⁻¹⌋₊ + 2)) * delta ^ 2 < epsilon ^ 2)
    (haffine : ∀ u ≤ 0, ∀ z v w,
      B u z v w = (1 + 2 * u) * B 0 z v w - 2 * u * B (-1 / 2) z v w) :
    RoundCylinderFamilyClose epsilon (Ioc (-(1 + eta)) 0) B := by
  obtain ⟨hs, b, hb, hbound⟩ := h.restrict_bound hd hde
    (fun u hu => hu.2.trans_lt zero_lt_one)
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by norm_num
  have hhalf : (-1 / 2 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by norm_num
  have hs0 := hs 0 hzero
  have hsh := hs (-1 / 2) hhalf
  refine ⟨?_, ((⌊epsilon⁻¹⌋₊ + 1 : ℕ) : ℝ) *
    (18 + 32 * 2 ^ (⌊epsilon⁻¹⌋₊ + 2)) * delta ^ 2, hsmall, ?_⟩
  · intro u hu q a b
    have hcoeff : (fun p : RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient (B u) (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) =
        fun p => (1 + 2 * u) * roundCylinderTensorCoefficient (B 0)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b -
          2 * u * roundCylinderTensorCoefficient (B (-1 / 2))
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b := by
      funext p
      exact haffine u hu.2 _ _ _
    rw [hcoeff]
    exact (contDiffOn_const.mul (hs0 q a b)).sub (contDiffOn_const.mul (hsh q a b))
  · intro u hu z hz
    exact M35.roundCylinderJetErrorSquared_time_affine_le B haffine epsilon hs0 hsh
      ⌊epsilon⁻¹⌋₊ u ⟨by linarith [hu.1], hu.2⟩ z hz (delta ^ 2) (sq_nonneg delta)
      ((hbound 0 hzero z hz).trans hb.le) ((hbound (-1 / 2) hhalf z hz).trans hb.le)

end PoincareConjecture.RoundCylinderFamilyClose

namespace PoincareConjecture.M35



theorem exists_affine_window_accuracy (epsilon d : ℝ) (he : 0 < epsilon) (hd : 0 < d) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ epsilon ∧ delta ≤ d ∧
      ((⌊epsilon⁻¹⌋₊ + 1 : ℕ) : ℝ) *
        (18 + 32 * 2 ^ (⌊epsilon⁻¹⌋₊ + 2)) * delta ^ 2 < epsilon ^ 2 := by
  let C : ℝ := ((⌊epsilon⁻¹⌋₊ + 1 : ℕ) : ℝ) *
    (18 + 32 * 2 ^ (⌊epsilon⁻¹⌋₊ + 2))
  have hlim : Tendsto (fun delta : ℝ => C * delta ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun delta : ℝ => C * delta ^ 2) 0 := by fun_prop
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠ delta : ℝ in 𝓝[>] 0, 0 < delta := self_mem_nhdsWithin
  have hsmall := hlim.eventually (Iio_mem_nhds (sq_pos_of_pos he))
  have hless : ∀ᶠ delta : ℝ in 𝓝[>] 0, delta < min epsilon d :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min he hd))
  obtain ⟨delta, hdelta, hbound, hlimit⟩ := (hpositive.and (hsmall.and hless)).exists
  exact ⟨delta, hdelta, (hlimit.trans_le (min_le_left _ _)).le,
    (hlimit.trans_le (min_le_right _ _)).le, hbound⟩

end PoincareConjecture.M35
