




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.CutoffEnergy
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Bootstrap








open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

private theorem compact_product_integrable {g h : Spacetime n → ℝ}
    (hg : Continuous g) (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun z => g z * h z) :=
  (hg.mul hh).integrable_of_hasCompactSupport hc.mul_left

private theorem compact_square_integrable {g : Spacetime n → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) : Integrable (fun z => g z ^ 2) := by
  simpa only [pow_two] using compact_product_integrable hg hg hc

private theorem compact_sum_support {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, HasCompactSupport (g i)) : HasCompactSupport (fun z => ∑ i, g i z) := by
  rw [show (fun z => ∑ i, g i z) = ∑ i, g i by funext z; simp only [Finset.sum_apply]]
  exact HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hg i)


theorem parabolic_cutoff_gradient_energy
    {a : Fin n → Fin n → Spacetime n → ℝ}
    {F : Fin n → Spacetime n → ℝ} {u f χ : Spacetime n → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hEll : ∀ z ∈ tsupport χ, ∀ ξ : Euclid n,
      κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j z * ξ i * ξ j)
    (heq : ∀ z ∈ tsupport χ, timeDeriv u z -
      ∑ i, spatialDeriv i (fun y => ∑ j, a i j y * spatialDeriv j u y) z =
      f z + ∑ i, spatialDeriv i (F i) z) :
    (κ / 2) * (∫ z, ∑ i, (χ z * spatialDeriv i u z) ^ 2) ≤
      (∫ z, χ z ^ 2 * f z * u z) + (∫ z, χ z * timeDeriv χ z * u z ^ 2) -
        2 * (∫ z, ∑ i, χ z * u z * F i z * spatialDeriv i χ z) +
        (1 / (2 * κ)) * (∫ z, ∑ i,
          (χ z * F i z + 2 * u z * ∑ j, spatialDeriv j χ z * a j i z) ^ 2) := by
  let G : Fin n → Spacetime n → ℝ := fun i z => χ z * spatialDeriv i u z
  let R : Fin n → Spacetime n → ℝ := fun i z => ∑ j, spatialDeriv j χ z * a j i z
  let P : Fin n → Spacetime n → ℝ := fun i z => χ z * F i z + 2 * u z * R i z
  have hG (i : Fin n) : ContDiff ℝ ∞ (G i) := hχ.mul (contDiff_spatialDeriv hu i)
  have hGc (i : Fin n) : HasCompactSupport (G i) := hχc.mul_right
  have hR (i : Fin n) : ContDiff ℝ ∞ (R i) :=
    ContDiff.sum (fun j _ => (contDiff_spatialDeriv hχ j).mul (ha j i))
  have hRc (i : Fin n) : HasCompactSupport (R i) :=
    compact_sum_support (fun j => (hasCompactSupport_spatialDeriv j hχc).mul_right)
  have hP (i : Fin n) : ContDiff ℝ ∞ (P i) :=
    (hχ.mul (hF i)).add ((contDiff_const.mul hu).mul (hR i))
  have hPc (i : Fin n) : HasCompactSupport (P i) := by
    change HasCompactSupport (χ * F i + (fun z => 2 * u z) * R i)
    exact hχc.mul_right.add (hRc i).mul_left
  have hGG (i : Fin n) := compact_square_integrable (hG i).continuous (hGc i)
  have hPP (i : Fin n) := compact_square_integrable (hP i).continuous (hPc i)
  have hPG (i : Fin n) := compact_product_integrable (hP i).continuous (hG i).continuous (hGc i)
  have henergy := parabolic_cutoff_energy_identity ha hF hu hf hχ hχc heq
  have hE : Integrable (fun z => ∑ i, ∑ j, a i j z * G i z * G j z) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      compact_product_integrable ((ha i j).continuous.mul (hG i).continuous)
        (hG j).continuous (hGc j)))
  have hpoint (z : Spacetime n) :
      κ * (∑ i, G i z ^ 2) ≤ ∑ i, ∑ j, a i j z * G i z * G j z := by
    by_cases hz : z ∈ tsupport χ
    · simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using
        hEll z hz (WithLp.toLp 2 (fun i => G i z))
    · simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hmono := integral_mono_ae
    ((integrable_finsetSum _ (fun i _ => hGG i)).const_mul κ) hE
    (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hmono
  have hEeq : (fun z => ∑ i, ∑ j, a i j z * G i z * G j z) =
      (fun z => ∑ i, ∑ j, χ z ^ 2 * a i j z * spatialDeriv i u z * spatialDeriv j u z) := by
    funext z
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [G]
    ring
  rw [hEeq, henergy] at hmono
  have hflux : |∫ z, ∑ i, P i z * G i z| ≤
      (κ / 2) * (∫ z, ∑ i, G i z ^ 2) +
        (1 / (2 * κ)) * (∫ z, ∑ i, P i z ^ 2) := by
    rw [integral_finsetSum _ (fun i _ => hPG i),
      integral_finsetSum _ (fun i _ => hGG i), integral_finsetSum _ (fun i _ => hPP i)]
    calc
      |∑ i, ∫ z, P i z * G i z| ≤ ∑ i, |∫ z, P i z * G i z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ((κ / 2) * (∫ z, G i z ^ 2) +
          (1 / (2 * κ)) * (∫ z, P i z ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [show 4 * (κ / 2) = 2 * κ by ring] using
          young_flux_absorption (show 0 < κ / 2 by positivity) (hPP i) (hGG i) (hPG i)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hA (i : Fin n) : Integrable (fun z => χ z ^ 2 * F i z * spatialDeriv i u z) := by
    convert compact_product_integrable (hχ.mul (hF i)).continuous (hG i).continuous (hGc i) using 1
    funext z
    dsimp only [G]
    ring
  have hD (i j : Fin n) : Integrable (fun z =>
      χ z * u z * spatialDeriv i χ z * a i j z * spatialDeriv j u z) := by
    convert compact_product_integrable
      ((hu.mul (contDiff_spatialDeriv hχ i)).mul (ha i j)).continuous
      (hG j).continuous (hGc j) using 1
    funext z
    dsimp only [G]
    ring
  have hJ : (fun z => ∑ i, P i z * G i z) =
      (fun z => (∑ i, χ z ^ 2 * F i z * spatialDeriv i u z) +
        2 * (∑ i, ∑ j, χ z * u z * spatialDeriv i χ z * a i j z * spatialDeriv j u z)) := by
    funext z
    simp only [P, G, add_mul, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp only [R, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [hJ, integral_add (integrable_finsetSum _ (fun i _ => hA i))
    ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hD i j))).const_mul 2),
    integral_const_mul] at hflux
  change (κ / 2) * (∫ z, ∑ i, G i z ^ 2) ≤ _ +
    (1 / (2 * κ)) * (∫ z, ∑ i, P i z ^ 2)
  linarith [neg_le_abs ((∫ z, ∑ i, χ z ^ 2 * F i z * spatialDeriv i u z) +
    2 * (∫ z, ∑ i, ∑ j, χ z * u z * spatialDeriv i χ z * a i j z * spatialDeriv j u z))]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
