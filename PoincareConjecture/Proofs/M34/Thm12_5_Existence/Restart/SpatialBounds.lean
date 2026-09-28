import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Ellipticity
import PoincareConjecture.Proofs.M34.Standard.ClosedIntervalGronwall
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricFlowApproximation

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)] (A : MetricFlowApproximation ginit Mfamily)

noncomputable def interiorFlow (k : ℕ) : RicciFlow 3 (Mfamily k) (Ioo 0 A.time) := by
  have hne : (Ioo 0 A.time).Nontrivial := by
    refine ⟨A.time / 3, ⟨?_, ?_⟩, 2 * A.time / 3, ⟨?_, ?_⟩, ?_⟩ <;>
      linarith [A.time_pos]
  exact Poincare.Geometry.RicciFlow.Harnack.restrictFlow (A.flow k)
    Ioo_subset_Icc_self ordConnected_Ioo hne

theorem spatialJet_norm_le_exp (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ A.source k) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ s ∈ Ioo 0 A.time,
      ‖deriv (fun u => iteratedFDeriv ℝ m (A.coefficients k u) x) s‖ ≤
        C * (1 + ‖iteratedFDeriv ℝ m (A.coefficients k s) x‖))
    {t : ℝ} (ht : t ∈ Icc 0 A.time) :
    ‖iteratedFDeriv ℝ m (A.coefficients k t) x‖ ≤
      max ‖iteratedFDeriv ℝ m (A.coefficients k 0) x‖ 1 * Real.exp (2 * C * t) := by
  apply norm_le_exp_of_interior_affine_deriv_bound
    (f := fun u : ℝ => iteratedFDeriv ℝ m (A.coefficients k u) x)
    (T := A.time) (C := C)
  · exact A.continuousOn_spatialJet_time k m (x := x) hx
  · intro s hs
    exact A.differentiableAt_spatialJet_time k m (x := x) hx (t := s) hs
  · exact hC
  · exact hb
  · exact ht

set_option backward.isDefEq.respectTransparency false in

theorem exists_compact_spatialJet_bounds (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ m, ∀ k t, t ∈ Icc 0 A.time →
      ∀ x ∈ K, x ∈ A.source k →
        ‖iteratedFDeriv ℝ j (A.coefficients k t) x‖ ≤ B := by
  obtain ⟨a, b, ha, hb, hcoeff⟩ := A.exists_compact_ellipticity P hK
  induction m with
  | zero =>
      refine ⟨max b 1, le_max_right _ _, ?_⟩
      intro j hj k t ht x hx hsource
      have hjzero : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      exact (A.norm_coefficients_le k t x hb
        (fun v => (hcoeff k t ht x hx hsource v).2)).trans (le_max_left _ _)
  | succ q ih =>
      obtain ⟨B, hB, hlower⟩ := ih
      obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
        3 q A.curvature_bound (fun d => (A.bound_pos d).le) ha hb B hB
      have hinit : ∃ Z : ℝ, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ (q + 1) ginit.euclideanCoefficients x‖ ≤ Z :=
        hK.exists_bound_of_continuousOn
          (f := iteratedFDeriv ℝ (q + 1) ginit.euclideanCoefficients)
          (fun x _ => ((ginit.contDiffAt_euclideanCoefficients x).continuousAt_iteratedFDeriv
            (by exact_mod_cast le_top)).continuousWithinAt)
      obtain ⟨Z, hZ⟩ := hinit
      let E := max Z 1 * Real.exp (2 * C * A.time)
      refine ⟨max B E, hB.trans (le_max_left _ _), ?_⟩
      intro j hj k t ht x hx hsource
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · have hbound (s : ℝ) (hs : s ∈ Ioo 0 A.time) :
            ‖deriv (fun u => iteratedFDeriv ℝ (q + 1) (A.coefficients k u) x) s‖ ≤
              C * (1 + ‖iteratedFDeriv ℝ (q + 1) (A.coefficients k s) x‖) := by
          exact hevol (A.interiorFlow k) isOpen_Ioo (A.source_isOpen k)
            (A.chart_smooth k)
            (fun _ hy => A.chart_invertible k _ hy) hs hsource
            (fun v => (hcoeff k s (Ioo_subset_Icc_self hs) x hx hsource v).1)
            (fun v => (hcoeff k s (Ioo_subset_Icc_self hs) x hx hsource v).2)
            (fun d _ => A.curvature_le d k s (Ioo_subset_Icc_self hs) _)
            (fun d hd hdq =>
              (hlower d hdq k s (Ioo_subset_Icc_self hs) x hx hsource).trans
                (le_self_pow₀ hB (by omega)))
        have hgr := A.spatialJet_norm_le_exp k (q + 1) hsource hC hbound ht
        rw [A.spatialJet_zero k (q + 1) hsource] at hgr
        apply hgr.trans ((le_trans ?_ (le_max_right B E)))
        apply mul_le_mul (max_le_max (hZ x hx) le_rfl)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by positivity)))
          (Real.exp_pos _).le (by positivity)
      · exact (hlower j (by omega) k t ht x hx hsource).trans (le_max_left _ _)

end PoincareConjecture.M34.MetricFlowApproximation
