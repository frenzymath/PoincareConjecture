import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CoordinateEvolution
import PoincareConjecture.Proofs.M04.TensorNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

theorem exists_closed_coordinate_jet_estimates
    (n m : ℕ) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b Z H : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hZ : 1 ≤ Z) (hH : 0 ≤ H) :
    ∃ B L : ℝ, 1 ≤ B ∧ 0 ≤ L ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
        {l r : ℝ} (_hlr : l < r) (F : RicciFlow n M (Icc l r)), r - l ≤ H →
        ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ v,
          a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ v,
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ j ≤ m,
          (F.connection t).curvatureDerivativeNorm j (e x) ≤ K j) →
        (∀ x ∈ U, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j ((F.metric l).pullbackCoefficients e) x‖ ≤ Z) →
        ∀ j ≤ m, ∀ x ∈ U,
          (∀ t ∈ Icc l r,
            ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B) ∧
          (∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
            ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
              iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ L * |t - s|) := by
  induction m with
  | zero =>
      have hK0 := hK 0
      refine ⟨max b 1, 2 * (n : ℝ) ^ 3 * K 0 * b, le_max_right _ _,
        by positivity, ?_⟩
      intro M _ _ _ _ l r hlr F _ U hU e he _ _ hupper hcurv _ j hj x hx
      obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
      have hc : ∀ t ∈ Icc l r, ∀ y ∈ U,
          (F.connection t).curvatureTensorNorm (e y) ≤ K 0 := by
        intro t ht y hy
        simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using hcurv t ht y hy 0 le_rfl
      obtain ⟨hnorm, htime⟩ := closed_metric_zeroth_jet_estimates hlr hb (hK 0) F hU he
        hupper hc x hx
      exact ⟨fun t ht => (hnorm t ht).trans (le_max_left _ _), htime⟩
  | succ q ih =>
      obtain ⟨B₀, L₀, hB₀, hL₀, hprevious⟩ := ih
      obtain ⟨B₁, L₁, hB₁, hL₁, hnext⟩ :=
        exists_closed_spatial_succ_estimates n q K hK ha hb hB₀ hZ hH
      refine ⟨max B₀ B₁, max L₀ L₁, hB₀.trans (le_max_left _ _),
        hL₀.trans (le_max_left _ _), ?_⟩
      intro M _ _ _ _ l r hlr F htime U hU e he hi hlower hupper hcurv hinitial
      have hlow := hprevious hlr F htime hU he hi hlower hupper
        (fun t ht x hx j hj => hcurv t ht x hx j (by omega))
        (fun x hx j hj => hinitial x hx j (by omega))
      have hhigh := hnext hlr F htime hU he hi hlower hupper hcurv
        (fun t ht x hx j _ hj => (hlow j hj x hx).1 t ht)
        (fun x hx => hinitial x hx (q + 1) le_rfl)
      intro j hj x hx
      by_cases heq : j = q + 1
      · subst j
        obtain ⟨hnorm, hmod⟩ := hhigh x hx
        refine ⟨fun t ht => (hnorm t ht).trans (le_max_right _ _), ?_⟩
        intro s hs t ht
        exact (hmod s hs t ht).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      · obtain ⟨hnorm, hmod⟩ := hlow j (by omega) x hx
        refine ⟨fun t ht => (hnorm t ht).trans (le_max_left _ _), ?_⟩
        intro s hs t ht
        exact (hmod s hs t ht).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end PoincareConjecture.M44
