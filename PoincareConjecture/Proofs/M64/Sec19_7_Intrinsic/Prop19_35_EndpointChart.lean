import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointMeasure

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

def m64IntrinsicEndpointParameters
    (e : AnnulusCoordinates → AnnulusCoordinates) (height : ℝ → ℝ) (S : Set ℝ) : Set ℝ :=
  {b | b ∈ Ico (0 : ℝ) rampPeriod ∧
    ∃ a ∈ S, e !₂[a, height a] = intrinsicAnnulusBoundary 2 b}

theorem m64Intrinsic_endpoint_chart_measure_le
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : Differentiable ℝ e)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (hF : (F : AnnulusCoordinates → AnnulusCoordinates) = e)
    (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    {S : Set ℝ} (hS : MeasurableSet S) {height : ℝ → ℝ} (hh : Measurable height)
    (hsource : ∀ a ∈ S, !₂[a, height a] ∈ F.source)
    (hend : ∀ a ∈ S, ‖e !₂[a, height a]‖ = 2)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 a ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[a, height a])
          (fderiv ℝ e !₂[a, height a] v) (fderiv ℝ e !₂[a, height a] v)) :
    MeasurableSet (m64IntrinsicEndpointParameters e height S) ∧
      ENNReal.ofReal c * (∫⁻ a in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
        ∫⁻ b in m64IntrinsicEndpointParameters e height S,
          ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 b) := by
  classical
  let J := intrinsicAnnulusBoundary 2 ⁻¹' F.target
  let raw : ℝ → AnnulusCoordinates := F.symm ∘ intrinsicAnnulusBoundary 2
  have hbc := m64Intrinsic_contDiff_boundary (2 : ℝ)
  have hJ : IsOpen J := F.open_target.preimage hbc.continuous
  have hraw : ContDiffOn ℝ ∞ raw J :=
    hFi.comp hbc.contDiffOn (fun _ hs => hs)
  let gamma : ℝ → AnnulusCoordinates := J.piecewise raw 0
  have heq (b : ℝ) (hb : b ∈ J) : gamma b = raw b := by
    simp only [gamma, piecewise_eq_of_mem J raw 0 hb]
  have hgm : Measurable gamma := hraw.continuousOn.measurable_piecewise
    continuous_zero.continuousOn hJ.measurableSet
  have hg : ContDiffOn ℝ ∞ gamma J := hraw.congr (fun b hb => heq b hb)
  have hg0 : Measurable (fun b => gamma b 0) := by fun_prop
  have hg1 : Measurable (fun b => gamma b 1) := by fun_prop
  have hlift (b : ℝ) (hb : b ∈ J) : e (gamma b) = intrinsicAnnulusBoundary 2 b := by
    rw [heq b hb, ← hF]
    exact F.right_inv hb
  have hbase (a : ℝ) (ha : a ∈ S) (b : ℝ)
      (hab : e !₂[a, height a] = intrinsicAnnulusBoundary 2 b) :
      b ∈ J ∧ gamma b = !₂[a, height a] := by
    have hb : b ∈ J := by
      change intrinsicAnnulusBoundary 2 b ∈ F.target
      rw [← hab, ← hF]
      exact F.map_source (hsource a ha)
    refine ⟨hb, ?_⟩
    rw [heq b hb]
    change F.symm (intrinsicAnnulusBoundary 2 b) = !₂[a, height a]
    rw [← hab, ← hF]
    exact F.left_inv (hsource a ha)
  let B := (Ico (0 : ℝ) rampPeriod ∩ J) ∩
    {b | gamma b 0 ∈ S} ∩ {b | gamma b 1 = height (gamma b 0)}
  have hB : MeasurableSet B :=
    ((measurableSet_Ico.inter hJ.measurableSet).inter (hS.preimage hg0)).inter
      (measurableSet_eq_fun hg1 (hh.comp hg0))
  have hBJ : B ⊆ J := fun _ hb => hb.1.1.2
  have hBP : B ⊆ Ico (0 : ℝ) rampPeriod := fun _ hb => hb.1.1.1
  have hgraph (b : ℝ) (hb : b ∈ B) : gamma b 1 = height (gamma b 0) := hb.2
  have hrepr (b : ℝ) (hb : b ∈ B) : !₂[gamma b 0, height (gamma b 0)] = gamma b := by
    rw [← hgraph b hb]
    ext i
    fin_cases i <;> rfl
  have hBexact : B = m64IntrinsicEndpointParameters e height S := by
    ext b
    constructor
    · intro hb
      refine ⟨hBP hb, gamma b 0, hb.1.2, ?_⟩
      rw [hrepr b hb]
      exact hlift b (hBJ hb)
    · rintro ⟨hb, a, ha, hab⟩
      obtain ⟨hbJ, hgbase⟩ := hbase a ha b hab
      exact ⟨⟨⟨hb, hbJ⟩, by simpa only [mem_ofPred_eq, hgbase, Matrix.cons_val_zero] using ha⟩,
        by simp only [mem_ofPred_eq, hgbase, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]⟩
  have himage : (fun b => gamma b 0) '' B = S := by
    apply Subset.antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.1.2
    · intro a ha
      obtain ⟨b, hb, hab⟩ := m64Intrinsic_exists_boundary_parameter (hend a ha)
      obtain ⟨_, hgbase⟩ := hbase a ha b hab
      refine ⟨b, ?_, ?_⟩
      · rw [hBexact]
        exact ⟨hb, a, ha, hab⟩
      · simp only [hgbase, Matrix.cons_val_zero]
  have hlength := m64Intrinsic_lifted_endpoint_graph_measure_le N hJ hg
    (fun b _ => he (gamma b)) hlift hB hBJ hBP hgraph hc (by
      intro b hb v
      have h := hbound (gamma b 0) hb.1.2 v
      rw [hrepr b hb] at h
      exact h)
  rw [himage, hBexact] at hlength
  exact ⟨hBexact ▸ hB, hlength⟩

end PoincareConjecture
