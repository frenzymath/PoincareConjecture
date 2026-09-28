import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitStrongEquation
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false

open Filter

universe u

namespace PoincareConjecture

theorem m64_two_column_norm_sq_le_liminf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {u0 u1 : ℕ → E} {v0 v1 : E}
    (h0 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u0 v0)
    (h1 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u1 v1)
    {B0 B1 : ℝ} (hB0 : ∀ k, ‖u0 k‖ ^ 2 ≤ B0)
    (hB1 : ∀ k, ‖u1 k‖ ^ 2 ≤ B1) :
    ‖v0‖ ^ 2 + ‖v1‖ ^ 2 ≤
      liminf (fun k => ‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2) atTop := by
  have h0' :=
    Poincare.Analysis.Sobolev.WeakCompactness.norm_sq_le_liminf h0 hB0
  have h1' :=
    Poincare.Analysis.Sobolev.WeakCompactness.norm_sq_le_liminf h1 hB1
  have h0lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun k => ‖u0 k‖ ^ 2) :=
    isBoundedUnder_of ⟨0, fun k => sq_nonneg ‖u0 k‖⟩
  have h0upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun k => ‖u0 k‖ ^ 2) :=
    isBoundedUnder_of ⟨B0, hB0⟩
  have h1lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun k => ‖u1 k‖ ^ 2) :=
    isBoundedUnder_of ⟨0, fun k => sq_nonneg ‖u1 k‖⟩
  have h1upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun k => ‖u1 k‖ ^ 2) :=
    isBoundedUnder_of ⟨B1, hB1⟩
  exact (add_le_add h0' h1').trans
    (le_liminf_add h0lower h0upper h1lower h1upper.isCoboundedUnder_ge)

theorem m64_two_column_dirichlet_energy_le_liminf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {u0 u1 : ℕ → E} {v0 v1 : E}
    (h0 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u0 v0)
    (h1 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u1 v1)
    {B0 B1 : ℝ} (hB0 : ∀ k, ‖u0 k‖ ^ 2 ≤ B0)
    (hB1 : ∀ k, ‖u1 k‖ ^ 2 ≤ B1) :
    (‖v0‖ ^ 2 + ‖v1‖ ^ 2) / 2 ≤
      liminf (fun k => (‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2) / 2) atTop := by
  let q : ℕ → ℝ := fun k => ‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2
  have hq0 : ∀ k, 0 ≤ q k := by
    intro k
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hqB : ∀ k, q k ≤ B0 + B1 := by
    intro k
    exact add_le_add (hB0 k) (hB1 k)
  have hsum := m64_two_column_norm_sq_le_liminf h0 h1 hB0 hB1
  have hscaled : (1 / 2 : ℝ) * (‖v0‖ ^ 2 + ‖v1‖ ^ 2) ≤
      (1 / 2 : ℝ) * liminf q atTop :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hmul : (liminf (fun _ : ℕ => (1 / 2 : ℝ)) atTop) * liminf q atTop ≤
      liminf ((fun k => (1 / 2 : ℝ) * q k)) atTop := by
    apply le_liminf_mul
    · exact Eventually.of_forall (fun _ => by norm_num)
    · exact isBoundedUnder_of ⟨(1 / 2 : ℝ), fun _ => le_rfl⟩
    · exact Eventually.of_forall hq0
    · exact (isBoundedUnder_of ⟨B0 + B1, hqB⟩).isCoboundedUnder_ge
  calc
    (‖v0‖ ^ 2 + ‖v1‖ ^ 2) / 2 =
        (1 / 2 : ℝ) * (‖v0‖ ^ 2 + ‖v1‖ ^ 2) := by ring
    _ ≤ (1 / 2 : ℝ) * liminf q atTop := hscaled
    _ = (liminf (fun _ : ℕ => (1 / 2 : ℝ)) atTop) * liminf q atTop := by
      rw [liminf_const]
    _ ≤ liminf ((fun k => (1 / 2 : ℝ) * q k)) atTop := hmul
    _ = liminf (fun k => q k / 2) atTop := by
      congr 1
      funext k
      ring
    _ = liminf (fun k => (‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2) / 2) atTop := by
      rfl

theorem m64_weighted_column_energy_le_liminf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {u0 u1 : ℕ → E} {v0 v1 : E}
    (h0 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u0 v0)
    (h1 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u1 v1)
    {B0 B1 : ℝ} (hB0 : ∀ k, ‖u0 k‖ ^ 2 ≤ B0)
    (hB1 : ∀ k, ‖u1 k‖ ^ 2 ≤ B1)
    {energies : ℕ → ℝ} {energy_limit : ℝ}
    (he : ∀ k, energies k = (‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2) / 2)
    (he_limit : energy_limit = (‖v0‖ ^ 2 + ‖v1‖ ^ 2) / 2) :
    energy_limit ≤ liminf energies atTop := by
  rw [he_limit]
  have h := m64_two_column_dirichlet_energy_le_liminf h0 h1 hB0 hB1
  calc
    (‖v0‖ ^ 2 + ‖v1‖ ^ 2) / 2 ≤
        liminf (fun k => (‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2) / 2) atTop := h
    _ = liminf energies atTop := by
      apply liminf_congr
      exact Eventually.of_forall (fun k => (he k).symm)

theorem m64_integral_energy_le_liminf_of_weighted_columns
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {u0 u1 : ℕ → E} {v0 v1 : E}
    (h0 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u0 v0)
    (h1 : Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges u1 v1)
    {B0 B1 : ℝ} (hB0 : ∀ k, ‖u0 k‖ ^ 2 ≤ B0)
    (hB1 : ∀ k, ‖u1 k‖ ^ 2 ≤ B1)
    {seqEnergy : ℕ → ℝ} {limitEnergy : ℝ}
    (hseq : ∀ k, seqEnergy k = (‖u0 k‖ ^ 2 + ‖u1 k‖ ^ 2) / 2)
    (hlimit : limitEnergy = (‖v0‖ ^ 2 + ‖v1‖ ^ 2) / 2) :
    limitEnergy ≤ liminf seqEnergy atTop :=
  m64_weighted_column_energy_le_liminf h0 h1 hB0 hB1 hseq hlimit

end PoincareConjecture
