import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetStability
import PoincareConjecture.Proofs.M35.Thm12_28.NeckRestriction









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35




theorem cylinder_jet_difference_uniform
    (order : ℕ) (I : Set ℝ) (hI : IsCompact I) (hItime : ∀ u ∈ I, u < 1) (l : ℝ)
    (B C : ℕ → ℝ → RoundCylinderTwoTensor)
    (hB : ∀ k u, u ∈ I → ∀ q : UnitTwoSphere, ∀ s ∈ Icc (-l) l, ∀ a b : Fin 3,
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient (B k u)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s))
    (hC : ∀ k u, u ∈ I → ∀ q : UnitTwoSphere, ∀ s ∈ Icc (-l) l, ∀ a b : Fin 3,
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient (C k u)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s))
    (hjet : ∀ m ≤ order, ∀ a b : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ N : ℕ, ∀ k ≥ N, ∀ u ∈ I, ∀ q : UnitTwoSphere, ∀ s ∈ Icc (-l) l,
        ‖iteratedFDeriv ℝ m (fun y => roundCylinderTensorCoefficient (B k u)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
          roundCylinderTensorCoefficient (C k u)
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s)‖ < eta)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ u ∈ I, ∀ z : RoundCylinderSpace,
      z.2 ∈ Icc (-l) l → roundCylinderJetDifferenceSquared u (B k u) (C k u) order z < eta := by
  classical
  by_contra hn
  push Not at hn
  choose sigma hsigma u hu z hz hbad using hn
  have hsig : Tendsto sigma atTop atTop := tendsto_atTop_atTop.mpr
    (fun N => ⟨N, fun k hk => hk.trans (hsigma k)⟩)
  obtain ⟨p, hp, phi, hphi, hconv⟩ := (hI.prod isCompact_Icc).tendsto_subseq
    (x := fun k => (u k, (z k).2)) (fun k => ⟨hu k, hz k⟩)
  have hut : Tendsto (u ∘ phi) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hconv
  have hst : Tendsto (fun k => (z (phi k)).2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hconv
  have hsel := hsig.comp hphi.tendsto_atTop
  have hcoeff (m : ℕ) (hm : m ≤ order) (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y =>
        roundCylinderTensorCoefficient (B (sigma (phi k)) (u (phi k)))
          (chartAt (EuclideanSpace ℝ (Fin 2)) (z (phi k)).1) y a b -
        roundCylinderTensorCoefficient (C (sigma (phi k)) (u (phi k)))
          (chartAt (EuclideanSpace ℝ (Fin 2)) (z (phi k)).1) y a b)
        (0, (z (phi k)).2)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro d hd
    obtain ⟨N, hN⟩ := hjet m hm a b d hd
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hsel.eventually (eventually_ge_atTop N))
    refine ⟨K, fun k hk => ?_⟩
    simpa only [dist_zero_right] using hN (sigma (phi k)) (hK k hk)
      (u (phi k)) (hu (phi k)) (z (phi k)).1 (z (phi k)).2 (hz (phi k))
  have hnorm := roundCylinderJetDifferenceSquared_tendsto_zero order
    (u ∘ phi) (fun k => hItime _ (hu (phi k))) p.1 (hItime _ hp.1) hut
    (fun k => (z (phi k)).1)
    (fun k => B (sigma (phi k)) (u (phi k)))
    (fun k => C (sigma (phi k)) (u (phi k)))
    (fun k => (z (phi k)).2) p.2 hst
    (fun k => hB _ _ (hu (phi k)) _ _ (hz (phi k)))
    (fun k => hC _ _ (hu (phi k)) _ _ (hz (phi k))) hcoeff
  obtain ⟨k, hk⟩ := (hnorm.eventually (Iio_mem_nhds heta)).exists
  exact (not_lt_of_ge (hbad (phi k))) hk

end PoincareConjecture.M35

namespace PoincareConjecture.RoundCylinderFamilyClose




theorem perturb_of_jet_difference_le {delta epsilon eta : ℝ} {I : Set ℝ}
    {B C : ℝ → RoundCylinderTwoTensor} (hC : RoundCylinderFamilyClose delta I C)
    (hd : 0 < delta) (hde : delta ≤ epsilon) (hI : ∀ u ∈ I, u < 1)
    (hB : ∀ u ∈ I, RoundCylinderTensorSmoothOn epsilon (B u))
    (hmargin : 2 * delta ^ 2 + 2 * eta < epsilon ^ 2)
    (herr : ∀ u ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      M35.roundCylinderJetDifferenceSquared u (B u) (C u) ⌊epsilon⁻¹⌋₊ z ≤ eta) :
    RoundCylinderFamilyClose epsilon I B := by
  obtain ⟨_, bound, hb, hjet⟩ := hC.restrict_bound hd hde hI
  refine ⟨hB, 2 * bound + 2 * eta, (by linarith), ?_⟩
  intro u hu z hz
  exact (M35.roundCylinderJetErrorSquared_le_twice (hI u hu) (B u) (C u) _ z).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hjet u hu z hz) (by norm_num))
      (mul_le_mul_of_nonneg_left (herr u hu z hz) (by norm_num)))

end PoincareConjecture.RoundCylinderFamilyClose

namespace PoincareConjecture.M35




theorem cylinder_family_close_eventually_of_coefficient_jets
    {delta epsilon : ℝ} (hd : 0 < delta) (he : 0 < epsilon) (hde : delta ≤ epsilon / 4)
    (I : Set ℝ) (hI : IsCompact I) (hItime : ∀ u ∈ I, u < 1)
    (B : ℕ → ℝ → RoundCylinderTwoTensor) (C : ℝ → RoundCylinderTwoTensor)
    (hB : ∀ k u, u ∈ I → RoundCylinderTensorSmoothOn delta (B k u))
    (hC : RoundCylinderFamilyClose delta I C)
    (hjet : ∀ m ≤ ⌊epsilon⁻¹⌋₊, ∀ a b : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ N : ℕ, ∀ k ≥ N, ∀ u ∈ I, ∀ q : UnitTwoSphere, ∀ s ∈ Icc (-epsilon⁻¹) epsilon⁻¹,
        ‖iteratedFDeriv ℝ m (fun y => roundCylinderTensorCoefficient (B k u)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
          roundCylinderTensorCoefficient (C u)
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s)‖ < eta) :
    ∃ N : ℕ, ∀ k ≥ N, RoundCylinderFamilyClose epsilon I (B k) := by
  have hlt : delta < epsilon := by linarith
  have hinv : epsilon⁻¹ < delta⁻¹ := inv_strictAnti₀ hd hlt
  have hinside {s : ℝ} (hs : s ∈ Icc (-epsilon⁻¹) epsilon⁻¹) :
      s ∈ Ioo (-delta⁻¹) delta⁻¹ :=
    ⟨(neg_lt_neg hinv).trans_le hs.1, hs.2.trans_lt hinv⟩
  have hsmooth (D : RoundCylinderTwoTensor) (hD : RoundCylinderTensorSmoothOn delta D)
      (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Icc (-epsilon⁻¹) epsilon⁻¹) (a b : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient D
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s) := by
    apply (hD q a b).contDiffAt
    apply ((chartAt (EuclideanSpace ℝ (Fin 2)) q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial, hinside hs⟩
  obtain ⟨N, hN⟩ := cylinder_jet_difference_uniform ⌊epsilon⁻¹⌋₊ I hI hItime epsilon⁻¹
    B (fun _ => C) (fun k u hu => hsmooth (B k u) (hB k u hu))
    (fun _ u hu => hsmooth (C u) (hC.1 u hu)) hjet (epsilon ^ 2 / 8) (by positivity)
  refine ⟨N, fun k hk => hC.perturb_of_jet_difference_le
    (eta := epsilon ^ 2 / 8) hd hlt.le hItime ?_ ?_ ?_⟩
  · intro u hu q a b
    exact (hB k u hu q a b).mono
      (prod_mono subset_rfl (Ioo_subset_Ioo (neg_le_neg hinv.le) hinv.le))
  · have hsq := pow_le_pow_left₀ hd.le hde 2
    nlinarith [sq_pos_of_pos he]
  · intro u hu z hz
    exact (hN k hk u hu z ⟨hz.1.le, hz.2.le⟩).le

end PoincareConjecture.M35
