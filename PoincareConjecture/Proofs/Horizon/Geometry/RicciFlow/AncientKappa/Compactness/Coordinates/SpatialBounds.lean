import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.SpacetimeBounds

theorem norm_le_exp_of_affine_deriv_bound_Icc_reference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b τ C K D : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hτ : τ ∈ Icc a b) (hinit : ‖f τ‖ ≤ D)
    (hbound : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ C + K * ‖f t‖)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖f t‖ ≤ max D 1 * Real.exp ((C + K) * |t - τ|) := by
  have hab : a ≤ b := ht.1.trans ht.2
  rcases hab.eq_or_lt with hab | hab
  · have htτ : t = τ := by linarith [ht.1, ht.2, hτ.1, hτ.2]
    simpa [htτ] using hinit.trans (le_max_left D 1)
  have hbetween {s v : ℝ} (hs : s ∈ Ioo a b) (hv : v ∈ Ioo a b) :
      ‖f s‖ ≤ max ‖f v‖ 1 * Real.exp ((C + K) * |s - v|) := by
    let g : ℝ → E := fun w => f (w + v)
    have hmem {w : ℝ} (hw : w ∈ Ioo (a - v) (b - v)) : w + v ∈ Ioo a b := by
      constructor <;> linarith [hw.1, hw.2]
    have hg {w : ℝ} (hw : w ∈ Ioo (a - v) (b - v)) :
        HasDerivAt g (deriv f (w + v)) w := by
      simpa only [g, Function.comp_def, id_eq, one_smul] using
        (hf _ (hmem hw)).hasDerivAt.scomp w ((hasDerivAt_id w).add_const v)
    have h := norm_le_exp_of_affine_deriv_bound
      (convex_Ioo (a - v) (b - v))
      (show (0 : ℝ) ∈ Ioo (a - v) (b - v) by constructor <;> linarith [hv.1, hv.2])
      (fun w hw => (hg hw).differentiableAt) hC hK
      (show ‖g 0‖ ≤ ‖f v‖ by simp [g])
      (fun w hw => (hg hw).deriv ▸ hbound _ (hmem hw))
      (show s - v ∈ Ioo (a - v) (b - v) by constructor <;> linarith [hs.1, hs.2])
    simpa [g] using h
  have hinterior {s : ℝ} (hs : s ∈ Ioo a b) :
      ‖f s‖ ≤ max D 1 * Real.exp ((C + K) * |s - τ|) := by
    have hτclosure : τ ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    have hright : ContinuousWithinAt
        (fun v => max ‖f v‖ 1 * Real.exp ((C + K) * |s - v|)) (Ioo a b) τ := by
      have hc := (hcont τ hτ).mono Ioo_subset_Icc_self
      fun_prop
    have h := ContinuousWithinAt.closure_le hτclosure continuousWithinAt_const hright
      (fun v hv => hbetween hs hv)
    exact h.trans
      (mul_le_mul_of_nonneg_right (max_le_max hinit le_rfl) (Real.exp_nonneg _))
  have htclosure : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  apply ContinuousWithinAt.closure_le htclosure
    ((hcont t ht).norm.mono Ioo_subset_Icc_self) (by fun_prop)
  exact fun s hs => hinterior hs

theorem exists_ancient_chart_spatial_jet_bound_at_reference
    (n m : ℕ) (K Z : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a α b : ℝ} (hα : 0 < α) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0))
        {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible) →
        ∀ W : Set (EuclideanSpace ℝ (Fin n)), W ⊆ U →
        (∀ t ∈ Icc (-a) 0, ∀ x ∈ W, ∀ v,
          α * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j t, t ∈ Icc (-a) 0 → ∀ x ∈ W,
          (F.connection t).curvatureDerivativeNorm j (e x) ≤ K j) →
        ∀ {τ : ℝ}, τ ∈ Icc (-a) 0 →
        (∀ j x, x ∈ W → ‖iteratedFDeriv ℝ j ((F.metric τ).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ t ∈ Icc (-a) 0, ∀ x ∈ W, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B := by
  induction m with
  | zero =>
      refine ⟨b, hb, ?_⟩
      intro M _ _ _ F U hU e he hi W hWU hell hcurv τ hτ hreference t ht x hx j hj
      have hj0 : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
      · exact fun v w => (F.metric t).symm _ _ _
      · intro v
        rw [abs_of_nonneg (le_trans (by positivity) (hell t ht x hx v).1)]
        exact (hell t ht x hx v).2
  | succ q ih =>
      obtain ⟨B, hB, hprevious⟩ := ih
      let A : ℝ := max B 1
      have hA : 1 ≤ A := le_max_right _ _
      obtain ⟨C, hC, hevol⟩ := exists_affine_spatialJet_evolution_bound n q K hK hα hb A hA
      let E : ℝ := max (Z (q + 1)) 1 * Real.exp ((C + C) * a)
      have hE : 0 ≤ E := by dsimp only [E]; positivity
      refine ⟨max B E, le_max_of_le_left hB, ?_⟩
      intro M _ _ _ F U hU e he hi W hWU hell hcurv τ hτ hreference t ht x hx j hj
      have hlower := hprevious F hU he hi W hWU hell hcurv hτ hreference
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · apply le_trans _ (le_max_right B E)
        let Fneg := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
          (show Iio (0 : ℝ) ⊆ Iic 0 from fun s hs =>
            show s ≤ 0 from le_of_lt hs) ordConnected_Iio
          (show (Iio (0 : ℝ)).Nontrivial from
            ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
        have hjoint : ContDiffOn ℝ ∞
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              iteratedFDeriv ℝ (q + 1) ((F.metric z.1).pullbackCoefficients e) z.2)
            (Iic 0 ×ˢ U) := contDiffOn_spatialJet_within
          (F.contDiffOn_pullbackCoefficients_within hU he) (uniqueDiffOn_Iic 0) hU (q + 1)
        have hcont : ContinuousOn
            (fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x)
            (Icc (-a) 0) := by
          have htime : Continuous (fun u : ℝ => (u, x)) :=
            continuous_id.prodMk continuous_const
          exact hjoint.continuousOn.comp (f := fun u : ℝ => (u, x)) htime.continuousOn
            (show MapsTo (fun u : ℝ => (u, x)) (Icc (-a) 0) (Iic 0 ×ˢ U) from
              fun _ hu => ⟨hu.2, hWU hx⟩)
        have hdiff : ∀ s ∈ Ioo (-a) 0, DifferentiableAt ℝ
            (fun u => iteratedFDeriv ℝ (q + 1) ((F.metric u).pullbackCoefficients e) x) s := by
          intro s hs
          have hsm := contDiffOn_spatialJet
            (Fneg.contDiffOn_pullbackCoefficients isOpen_Iio hU he) isOpen_Iio hU (q + 1)
          exact ((hsm.contDiffAt (x := (s, x))
            ((isOpen_Iio.prod hU).mem_nhds ⟨hs.2, hWU hx⟩)).comp s
            (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        have hbound : ∀ s ∈ Ioo (-a) 0,
            ‖deriv (fun u => iteratedFDeriv ℝ (q + 1)
              ((F.metric u).pullbackCoefficients e) x) s‖ ≤
            C + C * ‖iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x‖ := by
          intro s hs
          have hsclosed : s ∈ Icc (-a) 0 := ⟨hs.1.le, hs.2.le⟩
          have h := hevol Fneg isOpen_Iio hU he hi hs.2 (hWU hx)
            (fun v => (hell s hsclosed x hx v).1) (fun v => (hell s hsclosed x hx v).2)
            (fun d _ => hcurv d s hsclosed x hx)
            (fun d hd hdq => (hlower s hsclosed x hx d hdq).trans
              ((le_max_left B 1).trans (by
                simpa only [pow_one] using pow_le_pow_right₀ hA hd)))
          simpa only [Fneg, Poincare.Geometry.RicciFlow.Harnack.restrictFlow, mul_add, mul_one] using h
        have hprop := norm_le_exp_of_affine_deriv_bound_Icc_reference hcont hdiff hC hC
          hτ (hreference (q + 1) x hx) hbound ht
        apply hprop.trans
        apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (le_max_right (Z (q + 1)) 1))
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hC)
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2, hτ.1, hτ.2]
      · exact (hlower t ht x hx j (by omega)).trans (le_max_left B E)

end PoincareConjecture.SpacetimeBounds
