import PoincareConjecture.Proofs.M09.SmoothChartJoin
import PoincareConjecture.Proofs.M09.SquareComparisonDensity








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_smoothJoin_uniform_density {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (α β : ℝ → M) (D : Set ℝ)
    (hD : IsOpen D) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β D)
    (htime : D ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (b c : ℝ) (hI : Set.Icc 0 b ⊆ D) (hc : c ∈ Set.Ioo 0 b) (heq : α c = β c) :
    ∃ r : ℝ, 0 < r ∧ r < c ∧ c + r < b ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ d, 0 < d → d < r → ∃ γ : ℝ → M,
        ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ D ∧
        Set.EqOn γ α (Set.Iic (c - d)) ∧ Set.EqOn γ β (Set.Ici (c + d)) ∧
        ∀ s ∈ Set.Icc (c - d) (c + d),
          |squareCurveActionDensity F T α s| ≤ C ∧
          |squareCurveActionDensity F T β s| ≤ C ∧
          |squareCurveActionDensity F T γ s| ≤ C := by
  let p := α c
  let e := chartAt E p
  let y := e p
  have hyp : y ∈ e.target := e.map_source (mem_chart_source E p)
  obtain ⟨R, hR, hRK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds hyp)
  let K := Metric.closedBall y R
  have hK : IsCompact K := isCompact_closedBall y R
  have hKt : K ⊆ e.target := hRK
  let W := (D ∩ α ⁻¹' e.source) ∩ (D ∩ β ⁻¹' e.source)
  have hW : IsOpen W := (hα.continuousOn.isOpen_inter_preimage hD e.open_source).inter
    (hβ.continuousOn.isOpen_inter_preimage hD e.open_source)
  have hcD : c ∈ D := hI (Set.Ioo_subset_Icc_self hc)
  have hcW : c ∈ W := by
    refine ⟨⟨hcD, mem_chart_source E p⟩, hcD, ?_⟩
    change β c ∈ e.source
    rw [← heq]
    exact mem_chart_source E p
  let f : ℝ → E := fun s ↦ e (α s)
  let g : ℝ → E := fun s ↦ e (β s)
  have hf : ContDiffOn ℝ ∞ f W :=
    (contMDiffOn_chart.comp (hα.mono (fun _ hs ↦ hs.1.1)) (fun _ hs ↦ hs.1.2)).contDiffOn
  have hg : ContDiffOn ℝ ∞ g W :=
    (contMDiffOn_chart.comp (hβ.mono (fun _ hs ↦ hs.2.1)) (fun _ hs ↦ hs.2.2)).contDiffOn
  let V := (W ∩ f ⁻¹' Metric.ball y R) ∩ ((W ∩ g ⁻¹' Metric.ball y R) ∩ Set.Ioo 0 b)
  have hV : IsOpen V := (hf.continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball).inter
    ((hg.continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball).inter isOpen_Ioo)
  have hcV : c ∈ V := by
    refine ⟨⟨hcW, ?_⟩, ⟨hcW, ?_⟩, hc⟩
    · exact Metric.mem_ball_self hR
    · change e (β c) ∈ Metric.ball (e (α c)) R
      rw [heq]
      exact Metric.mem_ball_self hR
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hcV)
  have hrI : Set.Icc (c - r) (c + r) ⊆ V := by
    simpa only [Real.closedBall_eq_Icc] using hrV
  have hleft := (hrI (show c - r ∈ Set.Icc (c - r) (c + r) from ⟨le_rfl, by linarith⟩)).2.2
  have hright := (hrI (show c + r ∈ Set.Icc (c - r) (c + r) from ⟨by linarith, le_rfl⟩)).2.2
  have hrc : r < c := by linarith [hleft.1]
  have hcrb : c + r < b := hright.2
  have hrW : Set.Icc (c - r) (c + r) ⊆ W := fun s hs ↦ (hrI hs).1.1
  have hrD : Set.Icc (c - r) (c + r) ⊆ D := fun s hs ↦ (hrW hs).1.1
  have hfK (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : f s ∈ K :=
    Metric.ball_subset_closedBall (hrI hs).1.2
  have hgK (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : g s ∈ K :=
    Metric.ball_subset_closedBall (hrI hs).2.1.2
  obtain ⟨L, _, hL⟩ := exists_smoothJoinBlend_uniform_deriv_bound f g W hW hf hg c r hr hrW
    (congrArg e heq)
  obtain ⟨Cj, hCj, hCjb⟩ := squareChartActionDensity_bounded F hM04 T τmax hτmax hwindow p
    (Set.Icc (c - r) (c + r)) K isCompact_Icc hK (hrD.trans htime) hKt L
  have hda := squareCurveActionDensity_contDiffOn F hM04 T τmax hτmax hwindow α D hD hα htime
  have hdb := squareCurveActionDensity_contDiffOn F hM04 T τmax hτmax hwindow β D hD hβ htime
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn (hda.continuousOn.mono hI)
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn (hdb.continuousOn.mono hI)
  let C := |Cj| + |Ca| + |Cb|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCaC : Ca ≤ C := by dsimp [C]; linarith [le_abs_self Ca, abs_nonneg Cj, abs_nonneg Cb]
  have hCbC : Cb ≤ C := by dsimp [C]; linarith [le_abs_self Cb, abs_nonneg Cj, abs_nonneg Ca]
  have hCjC : Cj ≤ C := by dsimp [C]; linarith [le_abs_self Cj, abs_nonneg Ca, abs_nonneg Cb]
  refine ⟨r, hr, hrc, hcrb, C, hC, ?_⟩
  intro d hd hdr
  let γ := smoothChartJoin (n := n) α β p c r d
  let k := smoothJoinBlend f g c d
  have hkK (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : k s ∈ K :=
    smoothJoinBlend_mem_convex f g c d s K (convex_closedBall y R) (hfK s hs) (hgK s hs)
  have hαs (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : α s ∈ e.source := (hrW hs).1.2
  have hβs (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : β s ∈ e.source := (hrW hs).2.2
  have hγ := smoothChartJoin_contMDiffOn α β p c r d hr hd hdr D hD hrD hα hβ hαs hβs
    (fun s hs ↦ hKt (hkK s (Set.Ioo_subset_Icc_self hs)))
  refine ⟨γ, hγ, ?_, ?_, ?_⟩
  · intro s hs
    exact smoothChartJoin_eq_left α β p c r d hr hd hαs s hs
  · intro s hs
    exact smoothChartJoin_eq_right α β p c r d hr hd hβs s hs
  · intro s hs
    have hsI : s ∈ Set.Icc (c - r) (c + r) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hsO : s ∈ Set.Ioo (c - r) (c + r) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hsB : s ∈ Set.Icc 0 b := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine ⟨(hCa s hsB).trans hCaC, (hCb s hsB).trans hCbC, ?_⟩
    have he : γ =ᶠ[𝓝 s] (fun t ↦ e.symm (k t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hsO] with t ht
      exact smoothChartJoin_eq_middle α β p c r d t (Set.Ioo_subset_Icc_self ht)
    have hkd : HasDerivAt k (deriv k s) s :=
      (((smoothJoinBlend_contDiffOn f g c d W hf hg).contDiffAt
        (hW.mem_nhds (hrW hsI))).differentiableAt (by simp)).hasDerivAt
    rw [squareCurveActionDensity_congr F T γ _ s he,
      squareCurveActionDensity_inverseChart F T p k s (deriv k s) hkd (hKt (hkK s hsI))]
    exact (hCjb s hsI (k s) (hkK s hsI) (deriv k s) (hL d hd hdr.le s hs)).trans hCjC

end PoincareConjecture.Proofs.M09
