import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.EndpointGronwall
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.SpatialContinuity
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.InteriorEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M28

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in

theorem eventually_spatial_bounds_closed_backward
    {n : ℕ} {α : Type*} {M : α → Type*}
    [∀ w, TopologicalSpace (M w)]
    [∀ w, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M w)]
    [∀ w, IsManifold (𝓡 n) ∞ (M w)]
    (l : Filter α) {tau : ℝ} (htau : 0 < tau)
    (F : ∀ w, RicciFlow n (M w) (Icc (-tau) 0))
    (U V : α → Set (EuclideanSpace ℝ (Fin n)))
    (e : ∀ w, EuclideanSpace ℝ (Fin n) → M w)
    (hU : ∀ w, IsOpen (U w)) (hVU : ∀ w, V w ⊆ U w)
    (he : ∀ w, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e w) (U w))
    (hi : ∀ w y, y ∈ U w → (mfderiv (𝓡 n) (𝓡 n) (e w) y).IsInvertible)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hell : ∀ᶠ w in l, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V w, ∀ v,
      a * ‖v‖ ^ 2 ≤ ((F w).metric t).pullbackCoefficients (e w) x v v ∧
        ((F w).metric t).pullbackCoefficients (e w) x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : ∀ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ w in l,
      ∀ t ∈ Ioo (-tau) 0, ∀ x ∈ V w,
        ((F w).connection t).curvatureDerivativeNorm s (e w x) ≤ K)
    (hinit : ∀ m, ∃ Z : ℝ, 0 ≤ Z ∧ ∀ᶠ w in l, ∀ x ∈ V w,
      ‖iteratedFDeriv ℝ m (((F w).metric 0).pullbackCoefficients (e w)) x‖ ≤ Z) :
    ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l,
      ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V w, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (((F w).metric t).pullbackCoefficients (e w)) x‖ ≤ B := by
  intro m
  induction m with
  | zero =>
      refine ⟨b, hb, hell.mono ?_⟩
      intro w hw t ht x hx j hj
      have hj0 : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      exact norm_pullbackCoefficients_le_of_quadratic_upper _ _ _ hb
        (fun v => (hw t ht x hx v).2)
  | succ q ih =>
      obtain ⟨B, hB, hlower⟩ := ih
      let A : ℝ := max B 1
      have hA : 1 ≤ A := le_max_right _ _
      choose K hK hcurvBound using hcurv
      obtain ⟨C, hC, hevol⟩ := exists_affine_spatialJet_evolution_bound_interior
        n q K hK ha hb A hA
      obtain ⟨Z, _hZ, hzero⟩ := hinit (q + 1)
      let E : ℝ := max Z 1 * Real.exp ((C + C) * tau)
      have hE : 0 ≤ E := by dsimp [E]; positivity
      refine ⟨max B E, le_max_of_le_left hB, ?_⟩
      filter_upwards [hlower, hzero, hell,
        (eventually_all_finite (Set.finite_Iic (q + 1))).mpr
          (fun s _ => hcurvBound s)] with w hw hw0 hwell hwcurv
      intro t ht x hx j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hjq
      · have hxU : x ∈ U w := hVU w hx
        let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
          ContinuousLinearMap.toNormedAddCommGroup
        let : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
          ContinuousLinearMap.toNormedSpace
        let : NormedAddCommGroup
            (EuclideanSpace ℝ (Fin n) →L[ℝ]
              EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
          ContinuousLinearMap.toNormedAddCommGroup
        let : NormedSpace ℝ
            (EuclideanSpace ℝ (Fin n) →L[ℝ]
              EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
          ContinuousLinearMap.toNormedSpace
        let f : ℝ → EuclideanSpace ℝ (Fin n) [×(q + 1)]→L[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ]
              EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
          fun s => iteratedFDeriv ℝ (q + 1)
            (((F w).metric s).pullbackCoefficients (e w)) x
        have hcont : ContinuousOn
            f (Icc (-tau) 0) := by
          dsimp [f]
          exact continuousOn_time_spatialJet_of_within
            (uniqueDiffOn_Icc (by linarith : -tau < 0)) (hU w)
            ((F w).smooth.contDiffOn_spacetime_pullbackCoefficients_within (hU w) (he w))
            (q + 1) hxU
        have hdiff : ∀ s ∈ Ioo (-tau) 0, DifferentiableAt ℝ
            f s := by
          intro s hs
          dsimp [f]
          exact differentiableAt_spatialJet_of_mem_interior (F w) (hU w) (he w)
            (by simpa only [interior_Icc] using hs) (q + 1) hxU
        have hbound : ∀ s ∈ Ioo (-tau) 0,
            ‖deriv f s‖ ≤ C + C * ‖f s‖ := by
          intro s hs
          dsimp [f]
          have hscc := Ioo_subset_Icc_self hs
          have h := hevol (F w) (hU w) (he w) (hi w)
            (by simpa only [interior_Icc] using hs) hxU
            (fun v => (hwell s hscc x hx v).1)
            (fun v => (hwell s hscc x hx v).2)
            (fun d hd => hwcurv d hd s hs x hx)
            (fun d hd hdq => (hw s hscc x hx d hdq).trans
              ((le_max_left B 1).trans (by
                simpa only [pow_one] using pow_le_pow_right₀ hA hd)))
          simpa only [mul_add, mul_one] using h
        have hprop := norm_le_exp_of_affine_deriv_bound_closed_backward (f := f) htau.le
          hcont hdiff hC hC (hw0 x hx) hbound ht
        exact hprop.trans (le_max_right B E)
      · exact (hw t ht x hx j (by omega)).trans (le_max_left B E)

end PoincareConjecture.M28
