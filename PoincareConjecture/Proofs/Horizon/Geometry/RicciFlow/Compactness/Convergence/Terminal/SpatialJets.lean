import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Gronwall












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.SpacetimeBounds

private theorem norm_le_exp_of_affine_deriv_bound_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {l r σ : ℝ} (hσ : σ ∈ Icc l r)
    (hf : ∀ t ∈ Icc l r, DifferentiableAt ℝ f t)
    {C K D : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hinit : ‖f σ‖ ≤ D)
    (hbound : ∀ t ∈ Icc l r, ‖deriv f t‖ ≤ C + K * ‖f t‖)
    {t : ℝ} (ht : t ∈ Icc l r) :
    ‖f t‖ ≤ max D 1 * Real.exp ((C + K) * |t - σ|) := by
  let g : ℝ → E := fun s => f (s + σ)
  have hmem {s : ℝ} (hs : s ∈ Icc (l - σ) (r - σ)) : s + σ ∈ Icc l r := by
    constructor <;> linarith [hs.1, hs.2]
  have hg {s : ℝ} (hs : s ∈ Icc (l - σ) (r - σ)) :
      HasDerivAt g (deriv f (s + σ)) s := by
    simpa only [g, Function.comp_def, id_eq, one_smul] using
      (hf _ (hmem hs)).hasDerivAt.scomp s ((hasDerivAt_id s).add_const σ)
  have h := norm_le_exp_of_affine_deriv_bound (convex_Icc (l - σ) (r - σ))
    (show (0 : ℝ) ∈ Icc (l - σ) (r - σ) by constructor <;> linarith [hσ.1, hσ.2])
    (fun s hs => (hg hs).differentiableAt) hC hK
    (show ‖g 0‖ ≤ D by simpa [g] using hinit)
    (fun s hs => (hg hs).deriv ▸ hbound _ (hmem hs))
    (show t - σ ∈ Icc (l - σ) (r - σ) by constructor <;> linarith [ht.1, ht.2])
  simpa [g] using h




theorem exists_spatialJet_time_lipschitz_constant
    (n d : ℕ) (K Z : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type*} [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {J : Set ℝ} (F : RicciFlow n M J), IsOpen J →
        ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {l r σ : ℝ}, Icc l r ⊆ J → r - l ≤ 1 → σ ∈ Icc l r →
        ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ t ∈ Icc l r, ∀ v,
          a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j ≤ d, ∀ t ∈ Icc l r,
          (F.connection t).curvatureDerivativeNorm j (e x) ≤ K j) →
        (∀ j ≤ d, ‖iteratedFDeriv ℝ j ((F.metric σ).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ j ≤ d,
          (∀ t ∈ Icc l r,
            ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B) ∧
          (∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
            ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
              iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ B * |t - s|) := by
  induction d with
  | zero =>
      let C := 2 * (n : ℝ) ^ 3 * K 0 * b
      have hC : 0 ≤ C := by have := hK 0; dsimp [C]; positivity
      refine ⟨max b C, le_max_of_le_left hb, ?_⟩
      intro M _ _ _ _ J F hJ U hU e he hi l r σ hsub hlen hσ x hx hell hcurv hinit j hj
      have hj0 : j = 0 := by omega
      subst j
      have hnorm (t : ℝ) (ht : t ∈ Icc l r) :
          ‖(F.metric t).pullbackCoefficients e x‖ ≤ b := by
        apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
        · exact fun u v => (F.metric t).symm _ _ _
        · intro v
          have hn : 0 ≤ (F.metric t).pullbackCoefficients e x v v :=
            (mul_nonneg ha.le (sq_nonneg ‖v‖)).trans (hell t ht v).1
          rw [abs_of_nonneg hn]
          exact (hell t ht v).2
      refine ⟨fun t ht => ?_, ?_⟩
      · simpa only [norm_iteratedFDeriv_zero] using (hnorm t ht).trans (le_max_left b C)
      · intro s hs t ht
        have hd (u : ℝ) (hu : u ∈ Icc l r) :=
          F.differentiableAt_pullbackCoefficients_time hJ hU he (hsub hu) hx
        have hbnd (u : ℝ) (hu : u ∈ Icc l r) :
            ‖deriv (fun v => (F.metric v).pullbackCoefficients e x) u‖ ≤ C := by
          apply F.norm_deriv_pullbackCoefficients_le hJ hU he (hsub hu) hx hb (hK 0)
            (fun v => (hell u hu v).2)
          simpa only [LeviCivitaData.horizon_curvatureDerivativeNorm_zero] using hcurv 0 le_rfl u hu
        have h := (convex_Icc l r).norm_image_sub_le_of_norm_deriv_le hd hbnd hs ht
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map, Real.norm_eq_abs] using
          h.trans (mul_le_mul_of_nonneg_right (le_max_right b C) (abs_nonneg (t - s)))
  | succ q ih =>
      obtain ⟨B, hB, hprev⟩ := ih
      let D := max B 1
      have hD : 1 ≤ D := le_max_right _ _
      obtain ⟨C, hC, hevol⟩ := exists_affine_spatialJet_evolution_bound n q K hK ha hb D hD
      let E := max (Z (q + 1)) 1 * Real.exp (C + C)
      have hE : 0 ≤ E := by dsimp [E]; positivity
      let L := C * (1 + E)
      have hL : 0 ≤ L := by dsimp [L]; positivity
      refine ⟨max B (max E L), le_max_of_le_left hB, ?_⟩
      intro M _ _ _ _ J F hJ U hU e he hi l r σ hsub hlen hσ x hx hell hcurv hinit j hj
      have hp := hprev F hJ hU he hi hsub hlen hσ hx hell
        (fun k hk => hcurv k (by omega)) (fun k hk => hinit k (by omega))
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · have hd (t : ℝ) (ht : t ∈ Icc l r) : DifferentiableAt ℝ
            (fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x) t := by
          have hs := contDiffOn_spatialJet (F.contDiffOn_pullbackCoefficients hJ hU he) hJ hU (q + 1)
          exact ((hs.contDiffAt (x := (t, x)) ((hJ.prod hU).mem_nhds ⟨hsub ht, hx⟩)).comp t
            (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        have hevolution (t : ℝ) (ht : t ∈ Icc l r) :
            ‖deriv (fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x) t‖ ≤
              C * (1 + ‖iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x‖) := by
          apply hevol F hJ hU he hi (hsub ht) hx
            (fun v => (hell t ht v).1) (fun v => (hell t ht v).2)
            (fun k hk => hcurv k hk t ht)
          intro k hk hkq
          exact ((hp k hkq).1 t ht).trans ((le_max_left B 1).trans
            (by simpa only [pow_one] using pow_le_pow_right₀ hD hk))
        have hnorm (t : ℝ) (ht : t ∈ Icc l r) :
            ‖iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x‖ ≤ E := by
          have h := norm_le_exp_of_affine_deriv_bound_at hσ hd hC hC (hinit (q + 1) le_rfl)
            (fun s hs => by simpa only [mul_add, mul_one] using hevolution s hs) ht
          apply h.trans
          apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (le_max_right _ _))
          apply Real.exp_le_exp.mpr
          have habs : |t - σ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hσ.1, hσ.2]
          nlinarith
        have hbnd (t : ℝ) (ht : t ∈ Icc l r) :
            ‖deriv (fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x) t‖ ≤ L :=
          (hevolution t ht).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hnorm t ht)) hC)
        refine ⟨fun t ht => (hnorm t ht).trans ((le_max_left E L).trans (le_max_right B _)), ?_⟩
        intro s hs t ht
        have h := (convex_Icc l r).norm_image_sub_le_of_norm_deriv_le hd hbnd hs ht
        simpa only [Real.norm_eq_abs] using h.trans (mul_le_mul_of_nonneg_right
          ((le_max_right E L).trans (le_max_right B _)) (norm_nonneg (t - s)))
      · obtain ⟨hn, hl⟩ := hp j (by omega)
        exact ⟨fun t ht => (hn t ht).trans (le_max_left B _),
          fun s hs t ht => (hl s hs t ht).trans
            (mul_le_mul_of_nonneg_right (le_max_left B _) (abs_nonneg (t - s)))⟩

end PoincareConjecture.SpacetimeBounds
