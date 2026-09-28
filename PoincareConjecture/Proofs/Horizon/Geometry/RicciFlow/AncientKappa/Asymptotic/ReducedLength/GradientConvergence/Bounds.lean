import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.RescaledWeak
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Coercivity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff NNReal

universe u
namespace PoincareConjecture.AncientRescaling

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {s : ℝ} (R : AncientRescaling K s)

theorem reducedLengthCoordinateFlux_eq_neg_sum (p : M) (τ : ℝ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    R.reducedLengthCoordinateFlux p τ e i x =
      -(∑ j, LeviCivitaData.Dirichlet.divergenceCoefficients (R.flow.metric (-τ)) e x i j *
        fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) (s * τ)) x
          (EuclideanSpace.single j 1)) := by
  have h := LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing
    (g := R.flow.metric (-τ)) e x
    (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) (s * τ)) x)
    (EuclideanSpace.proj i)
  simp only [PiLp.proj_apply, PiLp.single_apply, mul_ite, mul_one, mul_zero] at h
  simp_rw [Finset.sum_ite_irrel] at h
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  unfold reducedLengthCoordinateFlux
  rw [neg_mul, ← h]

theorem abs_reducedLengthCoordinateFlux_le
    (p : M) (τ : ℝ) (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O) {L : ℝ≥0}
    (hlip : LipschitzOnWith L
      (fun y => reducedLength K.flow 0 p (e y) (s * τ)) O)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ x ∈ O, ∀ i j, |LeviCivitaData.Dirichlet.divergenceCoefficients
      (R.flow.metric (-τ)) e x i j| ≤ C)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ O) (i : Fin n) :
    |R.reducedLengthCoordinateFlux p τ e i x| ≤ (n : ℝ) * C * L := by
  rw [R.reducedLengthCoordinateFlux_eq_neg_sum, abs_neg]
  calc
    _ ≤ ∑ j, |LeviCivitaData.Dirichlet.divergenceCoefficients (R.flow.metric (-τ)) e x i j *
        fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) (s * τ)) x
          (EuclideanSpace.single j 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, C * (L : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul (hcoeff x hx i l)
        (Poincare.Analysis.Elliptic.abs_partial_le_of_lipschitzOn hO hlip hx l)
        (abs_nonneg _) hC
    _ = _ := by simp [mul_assoc]

theorem abs_reducedLengthCoordinateSource_le
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {x : EuclideanSpace ℝ (Fin n)} {B C : ℝ}
    (hl0 : 0 ≤ reducedLength K.flow 0 p (e x) (s * τ))
    (hlB : reducedLength K.flow 0 p (e x) (s * τ) ≤ B)
    (hρ : |(R.flow.metric (-τ)).pullbackVolumeDensity e x| ≤ C) :
    |R.reducedLengthCoordinateSource p τ e x| ≤ ((B + (n : ℝ) / 2) / τ) * C := by
  unfold reducedLengthCoordinateSource
  rw [abs_mul, abs_of_nonneg (div_nonneg (by positivity) hτ.le)]
  exact mul_le_mul (div_le_div_of_nonneg_right (add_le_add hlB le_rfl) hτ.le)
    hρ (abs_nonneg _) (div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]) hτ.le)

end PoincareConjecture.AncientRescaling
