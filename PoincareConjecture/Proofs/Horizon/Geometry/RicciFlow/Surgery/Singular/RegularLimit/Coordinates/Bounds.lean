import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Gronwall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Perturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

theorem uniform_spatial_metric_jet_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (hJ : IsOpen J)
    {T : ℝ} (hT : 0 < T) (htime : Ico 0 T ⊆ J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) (hAU : A ⊆ U)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hmetric : ∀ t ∈ Ico 0 T, ∀ x ∈ A, ∀ v,
      a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
        (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : ∀ k : ℕ, ∃ K : ℝ, ∀ t ∈ Ico 0 T, ∀ x ∈ A,
      (F.connection t).curvatureDerivativeNorm k (e x) ≤ K) :
    ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 T, ∀ x ∈ A,
      ‖iteratedFDeriv ℝ m ((F.metric t).pullbackCoefficients e) x‖ ≤ B := by
  choose K hK using hcurv
  have hall : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico 0 T, ∀ x ∈ A,
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B := by
    intro m
    induction m with
    | zero =>
        refine ⟨b, hb, ?_⟩
        intro t ht x hx j hj
        have hj0 : j = 0 := by omega
        subst j
        rw [norm_iteratedFDeriv_zero]
        apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
        · intro v w
          exact (F.metric t).symm (e x) _ _
        · intro v
          have h := hmetric t ht x hx v
          rw [abs_of_nonneg ((mul_nonneg ha.le (sq_nonneg ‖v‖)).trans h.1)]
          exact h.2
    | succ q ih =>
        obtain ⟨B, hB, hbound⟩ := ih
        let D : ℝ := max B 1
        have hD : 1 ≤ D := le_max_right _ _
        obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
          n q (fun j => max (K j) 0) (fun _ => le_max_right _ _) ha hb D hD
        obtain ⟨Z, hinit⟩ := hA.exists_bound_of_continuousOn
          (f := iteratedFDeriv ℝ (q + 1) ((F.metric 0).pullbackCoefficients e))
          (fun x hx => ((F.metric 0).contDiffAt_pullbackCoefficients
            (he.contMDiffAt (hU.mem_nhds (hAU hx)))).continuousAt_iteratedFDeriv
              (by exact_mod_cast le_top) |>.continuousWithinAt)
        let E : ℝ := max Z 1 * Real.exp ((C + C) * T)
        have hE : 0 ≤ E := by dsimp [E]; positivity
        refine ⟨max B E, le_max_of_le_left hB, ?_⟩
        intro t ht x hx j hj
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · have hdiff : ∀ s ∈ Ico 0 T, DifferentiableAt ℝ
              (fun u => iteratedFDeriv ℝ (q + 1)
                ((F.metric u).pullbackCoefficients e) x) s := by
            intro s hs
            have hjoint := SpacetimeBounds.contDiffOn_spatialJet
              (F.contDiffOn_pullbackCoefficients hJ hU he) hJ hU (q + 1)
            exact ((hjoint.contDiffAt (x := (s, x))
              ((hJ.prod hU).mem_nhds ⟨htime hs, hAU hx⟩)).comp s
                (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
          have hderiv : ∀ s ∈ Ico 0 T,
              ‖deriv (fun u => iteratedFDeriv ℝ (q + 1)
                ((F.metric u).pullbackCoefficients e) x) s‖ ≤
                  C + C * ‖iteratedFDeriv ℝ (q + 1)
                    ((F.metric s).pullbackCoefficients e) x‖ := by
            intro s hs
            have h := hevol F hJ hU he hi (htime hs) (hAU hx)
              (fun v => (hmetric s hs x hx v).1)
              (fun v => (hmetric s hs x hx v).2)
              (fun d _ => (hK d s hs x hx).trans (le_max_left _ _))
              (fun d hd hdq => (hbound s hs x hx d hdq).trans
                ((le_max_left B 1).trans
                  (by simpa only [pow_one] using pow_le_pow_right₀ hD hd)))
            simpa only [mul_add, mul_one] using h
          have hprop := SpacetimeBounds.norm_le_exp_of_affine_deriv_bound
            (convex_Ico 0 T) (show (0 : ℝ) ∈ Ico 0 T from ⟨le_rfl, hT⟩)
            hdiff hC hC (hinit x hx) hderiv ht
          apply hprop.trans
          apply le_trans _ (le_max_right B E)
          apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (le_max_right Z 1))
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hC)
          simpa only [abs_of_nonneg ht.1] using ht.2.le
        · exact (hbound t ht x hx j (by omega)).trans (le_max_left B E)
  intro m
  obtain ⟨B, hB, hbound⟩ := hall m
  exact ⟨B, hB, fun t ht x hx => hbound t ht x hx m le_rfl⟩

end PoincareConjecture.SingularRegularLimit
