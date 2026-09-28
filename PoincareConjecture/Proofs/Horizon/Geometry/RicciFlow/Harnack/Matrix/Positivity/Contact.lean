import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Matrix
open scoped Topology

namespace Poincare.RicciFlow.Harnack




lemma hasDerivWithinAt_quadratic_at_null
    {I : Type*} [Fintype I]
    {A : ℝ → Matrix I I ℝ} {A' : Matrix I I ℝ}
    {z : ℝ → I → ℝ} {z' : I → ℝ} {s : Set ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivWithinAt (fun r => A r i j) (A' i j) s t)
    (hz : ∀ i, HasDerivWithinAt (fun r => z r i) (z' i) s t)
    (hpos : (A t).PosSemidef) (hnull : z t ⬝ᵥ (A t *ᵥ z t) = 0) :
    HasDerivWithinAt (fun r => z r ⬝ᵥ (A r *ᵥ z r))
      (z t ⬝ᵥ (A' *ᵥ z t)) s t := by
  have hzero : A t *ᵥ z t = 0 :=
    (hpos.dotProduct_mulVec_zero_iff (z t)).mp (by simpa only [star_trivial] using hnull)
  have hright (i : I) : (∑ j, A t i j * z t j) = 0 := congrFun hzero i
  have hleft (j : I) : (∑ i, A t i j * z t i) = 0 := by
    have hs (i : I) : A t i j = A t j i := by
      simpa only [star_trivial] using hpos.1.apply j i
    simpa only [hs] using hright j
  have hcross₁ : (∑ i, ∑ j, z' i * A t i j * z t j) = 0 := by
    have hterm (i : I) : (∑ j, z' i * A t i j * z t j) = 0 := by
      rw [show (∑ j, z' i * A t i j * z t j) =
        z' i * (∑ j, A t i j * z t j) by simp only [Finset.mul_sum, mul_assoc]]
      rw [hright, mul_zero]
    simp only [hterm, Finset.sum_const_zero]
  have hcross₂ : (∑ i, ∑ j, z t i * A t i j * z' j) = 0 := by
    rw [Finset.sum_comm]
    have hterm (j : I) : (∑ i, z t i * A t i j * z' j) = 0 := by
      rw [← Finset.sum_mul]
      have hsum : (∑ i, z t i * A t i j) = 0 := by
        simpa only [mul_comm] using hleft j
      rw [hsum, zero_mul]
    simp only [hterm, Finset.sum_const_zero]
  have hd := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ =>
      ((hz i).mul (hA i j)).mul (hz j)
  simp only [Pi.mul_apply] at hd
  have heval (r : ℝ) : z r ⬝ᵥ (A r *ᵥ z r) =
      ∑ i, ∑ j, z r i * A r i j * z r j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [show (fun r => z r ⬝ᵥ (A r *ᵥ z r)) =
    (fun r => ∑ i, ∑ j, z r i * A r i j * z r j) by funext r; exact heval r]
  apply hd.congr_deriv
  simp only [add_mul, Finset.sum_add_distrib, hcross₁, hcross₂, zero_add, add_zero]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]




lemma quadratic_second_derivative_nonneg_at_null
    {I : Type*} [Fintype I]
    {A A' : ℝ → Matrix I I ℝ} {A'' : Matrix I I ℝ} {t : ℝ}
    (hA : ∀ᶠ r in 𝓝 t, ∀ i j, HasDerivAt (fun s => A s i j) (A' r i j) r)
    (hA' : ∀ i j, HasDerivAt (fun r => A' r i j) (A'' i j) t)
    (hpos : ∀ᶠ r in 𝓝 t, (A r).PosSemidef)
    (u v : I → ℝ) (hnull : u ⬝ᵥ (A t *ᵥ u) = 0) :
    0 ≤ u ⬝ᵥ (A'' *ᵥ u) +
      2 * (v ⬝ᵥ (A' t *ᵥ u) + u ⬝ᵥ (A' t *ᵥ v)) +
      2 * (v ⬝ᵥ (A t *ᵥ v)) := by
  let z : ℝ → I → ℝ := fun r i => u i + (r - t) * v i
  have hz (r : ℝ) (i : I) : HasDerivAt (fun s => z s i) (v i) r := by
    simpa only [z, id_eq, one_mul] using
      (((hasDerivAt_id r).sub_const t).mul_const (v i)).const_add (u i)
  have hzt (i : I) : z t i = u i := by simp [z]
  let f : ℝ → ℝ := fun r => ∑ i, ∑ j, z r i * A r i j * z r j
  let f' : ℝ → ℝ := fun r => ∑ i, ∑ j,
    ((v i * A r i j + z r i * A' r i j) * z r j + z r i * A r i j * v j)
  have hf : ∀ᶠ r in 𝓝 t, HasDerivAt f (f' r) r := by
    filter_upwards [hA] with r hr
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        ((hz r i).mul (hr i j)).mul (hz r j)
  have hdd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      ((((hA.self_of_nhds i j).const_mul (v i)).add
        ((hz t i).mul (hA' i j))).mul (hz t j)).add
        (((hz t i).mul (hA.self_of_nhds i j)).mul_const (v j))
  simp only [Pi.mul_apply, Pi.add_apply] at hdd
  have hmin : IsLocalMin f t := by
    filter_upwards [hpos] with r hr
    change f t ≤ f r
    have heq (s : ℝ) : f s = z s ⬝ᵥ (A s *ᵥ z s) := by
      simp only [f, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    rw [heq, show z t = u from funext hzt, hnull, heq]
    simpa only [star_trivial] using hr.dotProduct_mulVec_nonneg (z r)
  have hn := PoincareConjecture.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax
    hmin.neg hf.self_of_nhds.continuousAt.neg
  have hfirst : deriv (fun r => -f r) =ᶠ[𝓝 t] fun r => -f' r :=
    hf.mono fun r hr => hr.neg.deriv
  rw [hfirst.deriv_eq] at hn
  change deriv (-f') t ≤ 0 at hn
  rw [hdd.neg.deriv] at hn
  simp only [hzt] at hn
  have heq : (∑ i, ∑ j,
      (((v i * A' t i j + (v i * A' t i j + u i * A'' i j)) * u j +
        (v i * A t i j + u i * A' t i j) * v j) +
      (v i * A t i j + u i * A' t i j) * v j)) =
      u ⬝ᵥ (A'' *ᵥ u) + 2 * (v ⬝ᵥ (A' t *ᵥ u) + u ⬝ᵥ (A' t *ᵥ v)) +
        2 * (v ⬝ᵥ (A t *ᵥ v)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_add,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  linarith only [hn, heq]

end Poincare.RicciFlow.Harnack
