import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetStability

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

theorem full_cylinder_jet_difference_uniform
    (order : ℕ) (I : Set ℝ) (hI : IsCompact I) (hItime : ∀ u ∈ I, u < 1) (l : ℝ)
    (B C : ℕ → ℝ → RoundCylinderTwoTensor)
    (hB : ∀ k u, u ∈ I → ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-l) l, ∀ a b : Fin 3,
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient (B k u)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s))
    (hC : ∀ k u, u ∈ I → ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-l) l, ∀ a b : Fin 3,
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient (C k u)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s))
    (hjet : ∀ m ≤ order, ∀ a b : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ N : ℕ, ∀ k ≥ N, ∀ u ∈ I, ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-l) l,
        ‖iteratedFDeriv ℝ m (fun y => roundCylinderTensorCoefficient (B k u)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
          roundCylinderTensorCoefficient (C k u)
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s)‖ < eta)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ u ∈ I, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-l) l → roundCylinderJetDifferenceSquared u (B k u) (C k u) order z < eta := by
  classical
  by_contra hn
  push Not at hn
  choose sigma hsigma u hu z hz hbad using hn
  have hsig : Tendsto sigma atTop atTop := tendsto_atTop_mono hsigma tendsto_id
  obtain ⟨p, hp, phi, hphi, hconv⟩ := (hI.prod isCompact_Icc).tendsto_subseq
    (x := fun k => (u k, (z k).2)) (fun k => ⟨hu k, (hz k).1.le, (hz k).2.le⟩)
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
