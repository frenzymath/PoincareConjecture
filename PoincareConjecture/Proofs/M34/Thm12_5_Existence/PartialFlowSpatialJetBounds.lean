import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowFirstJetBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Perturbation

set_option autoImplicit false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in

theorem partialFlow_compactPullback_spatialJet_bounds (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ j ≤ m, ∀ {U : Set StandardCapSpace}, IsOpen U →
      ∀ {e : StandardCapSpace → StandardCapSpace}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U →
      (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) →
      (∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ t ∈ Ico 0 S, ∀ x ∈ K, x ∈ U →
        ‖iteratedFDeriv ℝ j ((F.flow.metric t).pullbackCoefficients e) x‖ ≤ G := by
  classical
  obtain ⟨a, b, ha, hb, hell⟩ := partialFlow_compactPullback_ellipticity P F hSF hB.le hfull hK
  choose C hC hderivs using fun k => partialFlow_curvatureDerivative_bound P E0 F
    hS hSF hB hfull k
  induction m with
  | zero =>
      refine ⟨max b 1, le_max_right _ _, ?_⟩
      intro j hj U _hU e _he _hinv hmetric t ht x hx hxU
      have hjzero : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      apply le_trans ?_ (le_max_left b 1)
      apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
      · intro u v
        exact (F.flow.metric t).symm _ _ _
      · intro v
        have hn : 0 ≤ (F.flow.metric t).pullbackCoefficients e x v v := by
          let w := mfderiv (𝓡 3) (𝓡 3) e x v
          change 0 ≤ (F.flow.metric t).inner (e x) w w
          by_cases hw : w = 0
          · simp [hw]
          · exact ((F.flow.metric t).pos _ _ hw).le
        rw [abs_of_nonneg hn]
        exact (hell t ht x hx e (hmetric x hxU) v).2
  | succ q ih =>
      obtain ⟨A, hA, hprev⟩ := ih
      obtain ⟨D, hD, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
        3 q C (fun k => (hC k).le) ha hb A hA
      obtain ⟨Z, hZ⟩ := hK.exists_bound_of_continuousOn
        (f := iteratedFDeriv ℝ (q + 1) g0.metric.euclideanCoefficients)
        (fun x _ => ((g0.metric.contDiffAt_euclideanCoefficients x).continuousAt_iteratedFDeriv
          (by exact_mod_cast le_top)).continuousWithinAt)
      let G := max Z 1 * Real.exp (2 * D * S)
      refine ⟨max A G, hA.trans (le_max_left _ _), ?_⟩
      intro j hj U hU e he hinv hmetric t ht x hx hxU
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · let c := fun t => (F.flow.metric t).pullbackCoefficients e
        have hcoeff := F.flow.smooth.contDiffOn_spacetime_pullbackCoefficients hU he
        have hjoint : ContDiffOn ℝ ∞
            (fun p : ℝ × StandardCapSpace => iteratedFDeriv ℝ (q + 1) (c p.1) p.2)
            (Ico 0 F.lifetime ×ˢ U) :=
          hcoeff.iteratedFDeriv_snd_of_isOpen hU (q + 1)
        have hsub : Ioo 0 S ⊆ Ico 0 F.lifetime :=
          fun _ hs => ⟨hs.1.le, hs.2.trans_le hSF⟩
        have hne : (Ioo 0 S).Nontrivial := by
          refine ⟨S / 3, ⟨?_, ?_⟩, 2 * S / 3, ⟨?_, ?_⟩, ?_⟩ <;> linarith
        let H := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F.flow hsub ordConnected_Ioo hne
        have hbound (s : ℝ) (hs : s ∈ Ioo 0 S) :
            ‖deriv (fun u => iteratedFDeriv ℝ (q + 1) (c u) x) s‖ ≤
              D * (1 + ‖iteratedFDeriv ℝ (q + 1) (c s) x‖) := by
          exact hevol H isOpen_Ioo hU he hinv hs hxU
            (fun v => (hell s ⟨hs.1.le, hs.2⟩ x hx e (hmetric x hxU) v).1)
            (fun v => (hell s ⟨hs.1.le, hs.2⟩ x hx e (hmetric x hxU) v).2)
            (fun k _ => hderivs k s ⟨hs.1.le, hs.2⟩ (e x))
            (fun k hk hkq => (hprev k hkq hU he hinv hmetric s ⟨hs.1.le, hs.2⟩ x hx hxU).trans
              (le_self_pow₀ hA (by omega)))
        let T := (t + S) / 2
        have htT : t ≤ T := by dsimp [T]; linarith [ht.2]
        have hTS : T < S := by dsimp [T]; linarith [ht.2]
        have hc : ContinuousOn (fun u => iteratedFDeriv ℝ (q + 1) (c u) x) (Icc 0 T) := by
          apply hjoint.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          exact fun _ hu => ⟨⟨hu.1, (hu.2.trans_lt hTS).trans_le hSF⟩, hxU⟩
        have hd (s : ℝ) (hs : s ∈ Ioo 0 T) :
            DifferentiableAt ℝ (fun u => iteratedFDeriv ℝ (q + 1) (c u) x) s := by
          have hreg := hjoint.mono (prod_mono hsub (Subset.refl U))
          have hat := hreg.contDiffAt (x := (s, x))
            ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨hs.1, hs.2.trans hTS⟩, hxU⟩)
          exact (hat.comp s (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        have hgr := norm_le_exp_of_interior_affine_deriv_bound hc hd hD
          (fun s hs => hbound s ⟨hs.1, hs.2.trans hTS⟩) ⟨ht.1, htT⟩
        have hzero : c 0 =ᶠ[𝓝 x] g0.metric.euclideanCoefficients := by
          filter_upwards [hU.mem_nhds hxU] with y hy
          dsimp only [c]
          rw [F.initial_metric]
          ext u v
          exact (hmetric y hy u v).symm
        rw [(hzero.iteratedFDeriv (𝕜 := ℝ) (q + 1)).eq_of_nhds] at hgr
        apply hgr.trans (le_trans ?_ (le_max_right A G))
        exact mul_le_mul (max_le_max (hZ x hx) le_rfl)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le (by positivity)))
          (Real.exp_pos _).le (by positivity)
      · exact (hprev j (by omega) hU he hinv hmetric t ht x hx hxU).trans (le_max_left _ _)

end PoincareConjecture.M34
