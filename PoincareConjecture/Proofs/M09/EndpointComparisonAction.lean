import PoincareConjecture.Proofs.M09.EndpointFamily
import PoincareConjecture.Proofs.M09.UnitIntervalAction
import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Statements.Ch06.LGeometry

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_local_smooth_comparison_action {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p q : M) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ∃ N : Set (M × ℝ), IsOpen N ∧ (q, b) ∈ N ∧
      N ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∃ B : M × ℝ → ℝ,
        ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B N ∧
        B (q, b) = 2 * Real.sqrt b * reducedLength F T p q b ∧
        ∀ w ∈ N, ∃ P : BackwardTimePath F T 0 w.2,
          P.curve 0 = p ∧ P.curve w.2 = w.1 ∧ backwardLLength F T 0 w.2 P.curve = B w := by
  obtain ⟨P, hP0, hPb, hPmin, hPl⟩ := hL.reduced_length_attained b hb hmax.le p q
  obtain ⟨R⟩ := hL.regularized_geodesic 0 b le_rfl hb hmax.le P
    (hL.euler_lagrange 0 b le_rfl hb hmax.le P hPmin)
  let H := Real.sqrt b
  have hH : 0 < H := Real.sqrt_pos.mpr hb
  let γ : ℝ → M := fun r ↦ R.path.curve (H * r)
  let D := (fun r : ℝ ↦ H * r) ⁻¹' R.path.domain
  have hi : ContDiff ℝ ∞ (fun r : ℝ ↦ H * r) := contDiff_const.mul contDiff_id
  have hD : IsOpen D := R.path.open_domain.preimage hi.continuous
  have hI : Set.Icc (0 : ℝ) 1 ⊆ D := by
    intro r hr
    apply R.path.interval_subset
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using
      (show H * r ∈ Set.Icc 0 H from
        ⟨mul_nonneg hH.le hr.1, mul_le_of_le_one_right hH.le hr.2⟩)
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ D :=
    R.path.smooth.comp hi.contMDiff.contMDiffOn (fun _ hr ↦ hr)
  have hγ0 : γ 0 = p := by
    have hr := R.path.agrees 0 (by simp [sqrtParameterInterval, Real.sqrt_nonneg b])
    have hr' : R.path.curve 0 = P.curve 0 := by simpa only [zero_pow two_ne_zero] using hr
    simpa only [γ, mul_zero] using hr'.trans hP0
  have hγ1 : γ 1 = q := by
    have hr := R.path.agrees H (by simp [sqrtParameterInterval, H, Real.sqrt_nonneg b])
    have hr' : R.path.curve H = P.curve b := by
      simpa only [H, Real.sq_sqrt hb.le] using hr
    simpa only [γ, mul_one] using hr'.trans hPb
  obtain ⟨f, U, V, hU, hV, hyV, hVtarget, hVU, hf, hstart, hend, hcenter⟩ :=
    exists_smooth_endpoint_family γ D hD hI hγ
  simp only [hγ0] at hstart
  simp only [hγ1] at hyV hVtarget hend hcenter
  let e := chartAt E q
  let c : M × ℝ → E × ℝ := fun w ↦ (e w.1, w.2)
  let Cdom : Set (M × ℝ) := e.source ×ˢ Set.univ
  let A : E × ℝ → ℝ := fun z ↦ backwardLLength F T 0 z.2
    (fun τ ↦ f (z.1, Real.sqrt τ / Real.sqrt z.2))
  let N := Cdom ∩ c ⁻¹' (V ×ˢ Set.Ioo 0 τmax)
  let B : M × ℝ → ℝ := fun w ↦ A (c w)
  have hc : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, E × ℝ)) ∞ c Cdom :=
    (contMDiffOn_chart.comp contMDiffOn_fst (fun w hw ↦ hw.1)).prodMk_space contMDiffOn_snd
  have hN : IsOpen N := hc.continuousOn.isOpen_inter_preimage
    (e.open_source.prod isOpen_univ) (hV.prod isOpen_Ioo)
  have hqN : (q, b) ∈ N := ⟨⟨mem_chart_source E q, Set.mem_univ _⟩, hyV, hb, hmax⟩
  have hA : ContDiffOn ℝ ∞ A (V ×ˢ Set.Ioo 0 τmax) :=
    contDiffOn_unitFamily_action F hM04 T τmax hτmax hwindow f U hU hf V hV hVU
  have hB : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B N :=
    hA.contMDiffOn.comp (hc.mono Set.inter_subset_left) (fun w hw ↦ hw.2)
  refine ⟨N, hN, hqN, (fun w hw ↦ ⟨Set.mem_univ _, hw.2.2⟩), B, hB, ?_, ?_⟩
  · have heq : Set.EqOn (fun τ ↦ f (e q, Real.sqrt τ / H)) P.curve (Set.Ioo 0 b) := by
      intro τ hτ
      have hr : Real.sqrt τ / H ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Real.sqrt_nonneg _) hH.le,
          (div_le_one hH).mpr (Real.sqrt_le_sqrt hτ.2.le)⟩
      change f ((chartAt E q) q, Real.sqrt τ / H) = P.curve τ
      rw [hcenter (Real.sqrt τ / H) hr]
      change R.path.curve (H * (Real.sqrt τ / H)) = P.curve τ
      rw [mul_div_cancel₀ _ hH.ne']
      have hs : Real.sqrt τ ∈ sqrtParameterInterval 0 b := by
        simpa only [sqrtParameterInterval, Real.sqrt_zero] using
          (show Real.sqrt τ ∈ Set.Icc 0 (Real.sqrt b) from
            ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hτ.2.le⟩)
      simpa only [Real.sq_sqrt hτ.1.le] using R.path.agrees (Real.sqrt τ) hs
    have haction := backwardLLength_congr_Ioo F T 0 b hb.le _ P.curve heq
    change backwardLLength F T 0 b (fun τ ↦ f (e q, Real.sqrt τ / H)) = _
    rw [haction, hPl, mul_div_cancel₀ _ (mul_pos zero_lt_two hH).ne']
  · intro w hw
    obtain ⟨Q, hQ⟩ := exists_backwardPath_of_unitFamily F hM04 T τmax hτmax hwindow
      f U hU hf (e w.1) (fun r hr ↦ hVU ⟨hw.2.1, hr⟩) w.2 hw.2.2.1 hw.2.2.2
    refine ⟨Q, ?_, ?_, ?_⟩
    · simp only [hQ, Real.sqrt_zero, zero_div, hstart]
    · rw [hQ]
      change f (e w.1, Real.sqrt w.2 / Real.sqrt w.2) = w.1
      rw [div_self (Real.sqrt_pos.mpr hw.2.2.1).ne', hend]
      exact e.left_inv hw.1.1
    · rw [hQ]

end PoincareConjecture.Proofs.M09
