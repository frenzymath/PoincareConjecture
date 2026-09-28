import PoincareConjecture.Statements.M44Providers
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M44




theorem exists_buffered_initial_derivative_bound
    (P : M44CapPersistencePredecessors.{u}) (n m : ℕ)
    {K H r : ℝ} (hK : 0 < K) (hH : 0 < H) (hr : 0 < r) :
    ∃ B : ℝ, 0 < B ∧ ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M],
      ∀ {T : ℝ}, 0 < T → T ≤ H → ∀ (F : RicciFlow n M (Icc 0 T)),
      (∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ j ≤ m, ∀ x : M, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
      ∀ p : M, IsCompact (closure ((F.metric 0).ball p r)) →
      ∀ j ≤ m, ∀ t ∈ Icc 0 T, (F.connection t).curvatureDerivativeNorm j p ≤ B := by
  choose C hC hbound using fun j : Fin (m + 1) =>
    P.curvature.initial_derivative_estimates n j.1 m K (K * H) r hK (mul_pos hK hH) hr
  let B := ∑ j : Fin (m + 1), C j
  have hB : 0 < B := Finset.sum_pos (fun j _ => hC j) Finset.univ_nonempty
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ _ T hT hTH F hcurv hinitial p hcompact j hj t ht
  have htime : T ≤ (K * H) / K := by simpa only [mul_div_cancel_left₀ _ hK.ne'] using hTH
  have hp : p ∈ (F.metric 0).ball p (r / 2) := by
    change (F.metric 0).edist p p < ENNReal.ofReal (r / 2)
    have hself : (F.metric 0).edist p p = 0 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨(F.metric 0).toRiemannianMetric⟩
      exact Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hh := hbound ⟨j, by omega⟩ M T hT htime F p hcompact hcurv hinitial
    t ht (Or.inr hj) p hp
  have hsum : C ⟨j, by omega⟩ ≤ B :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ _)
  apply le_trans _ hsum
  simpa only [Nat.sub_eq_zero_of_le hj, Nat.cast_zero, zero_div,
    Real.rpow_zero, div_one] using hh




theorem buffered_pullback_ellipticity
    (P : M44CapPersistencePredecessors.{u}) {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {T H K a b : ℝ} (hTH : T ≤ H) (hK : 0 ≤ K) (ha : 0 < a)
    (F : RicciFlow n M (Icc 0 T))
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (e : EuclideanSpace ℝ (Fin n) → M) {x : EuclideanSpace ℝ (Fin n)}
    (hlower : ∀ v, a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e x v v)
    (hupper : ∀ v, (F.metric 0).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) (v : EuclideanSpace ℝ (Fin n)) :
    (a * Real.exp (-2 * (n : ℝ) * K * H)) * ‖v‖ ^ 2 ≤
        (F.metric t).pullbackCoefficients e x v v ∧
      (F.metric t).pullbackCoefficients e x v v ≤
        (b * Real.exp (2 * (n : ℝ) * K * H)) * ‖v‖ ^ 2 := by
  have htime : 0 ≤ T := ht.1.trans ht.2
  have hc := P.curvature.metric_comparison n M (Icc 0 T) F 0 t K
    ⟨le_rfl, htime⟩ ht ht.1 hK
    (fun s hs => hcurv s ⟨hs.1, hs.2.trans ht.2⟩)
    (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
  change Real.exp (-2 * (n : ℝ) * K * (t - 0)) *
      (F.metric 0).pullbackCoefficients e x v v ≤
        (F.metric t).pullbackCoefficients e x v v ∧
    (F.metric t).pullbackCoefficients e x v v ≤
      Real.exp (2 * (n : ℝ) * K * (t - 0)) *
        (F.metric 0).pullbackCoefficients e x v v at hc
  have hnonneg : 0 ≤ (F.metric 0).pullbackCoefficients e x v v :=
    (mul_nonneg ha.le (sq_nonneg _)).trans (hlower v)
  have hexp : Real.exp (2 * (n : ℝ) * K * t) ≤ Real.exp (2 * (n : ℝ) * K * H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ht.2.trans hTH) (by positivity))
  have hexp' : Real.exp (-2 * (n : ℝ) * K * H) ≤ Real.exp (-2 * (n : ℝ) * K * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (ht.2.trans hTH)
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg n)) hK))
  simp only [sub_zero] at hc
  constructor
  · calc
      _ = Real.exp (-2 * (n : ℝ) * K * H) * (a * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-2 * (n : ℝ) * K * t) *
          (F.metric 0).pullbackCoefficients e x v v :=
        mul_le_mul hexp' (hlower v) (mul_nonneg ha.le (sq_nonneg _)) (Real.exp_pos _).le
      _ ≤ _ := hc.1
  · calc
      _ ≤ Real.exp (2 * (n : ℝ) * K * t) *
          (F.metric 0).pullbackCoefficients e x v v := hc.2
      _ ≤ Real.exp (2 * (n : ℝ) * K * H) * (b * ‖v‖ ^ 2) :=
        mul_le_mul hexp (hupper v) hnonneg (Real.exp_pos _).le
      _ = _ := by ring

end PoincareConjecture.M44
