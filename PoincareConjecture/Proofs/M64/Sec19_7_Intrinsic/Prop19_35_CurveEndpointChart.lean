import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurveEndpointMeasure











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



def m64IntrinsicCurveEndpointParameters
    (e : AnnulusCoordinates → AnnulusCoordinates) (height : ℝ → ℝ)
    (S : Set ℝ) (target : ℝ → AnnulusCoordinates) (T : Set ℝ) : Set ℝ :=
  {t | t ∈ T ∧ ∃ a ∈ S, e !₂[a, height a] = target t}



theorem m64Intrinsic_curve_endpoint_chart_measure_le
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : Differentiable ℝ e)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (hF : (F : AnnulusCoordinates → AnnulusCoordinates) = e)
    (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {height : ℝ → ℝ} (hh : Measurable height)
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    (htargetInj : InjOn target T)
    (hsource : ∀ a ∈ S, !₂[a, height a] ∈ F.source)
    (hend : ∀ a ∈ S, e !₂[a, height a] ∈ target '' T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 a ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[a, height a])
          (fderiv ℝ e !₂[a, height a] v) (fderiv ℝ e !₂[a, height a] v)) :
    MeasurableSet (m64IntrinsicCurveEndpointParameters e height S target T) ∧
      ENNReal.ofReal c * (∫⁻ a in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
        ∫⁻ t in m64IntrinsicCurveEndpointParameters e height S target T,
          ENNReal.ofReal (Real.sqrt
            (N.metric.inner (target t) (deriv target t) (deriv target t))) := by
  classical
  let J := target ⁻¹' F.target
  let raw : ℝ → AnnulusCoordinates := F.symm ∘ target
  have hJ : IsOpen J := F.open_target.preimage htarget.continuous
  have hraw : ContDiffOn ℝ ∞ raw J :=
    hFi.comp htarget.contDiffOn (fun _ hs => hs)
  let gamma : ℝ → AnnulusCoordinates := J.piecewise raw 0
  have heq (t : ℝ) (ht : t ∈ J) : gamma t = raw t := by
    simp only [gamma, piecewise_eq_of_mem J raw 0 ht]
  have hgm : Measurable gamma := hraw.continuousOn.measurable_piecewise
    continuous_zero.continuousOn hJ.measurableSet
  have hg : ContDiffOn ℝ ∞ gamma J := hraw.congr (fun t ht => heq t ht)
  have hg0 : Measurable (fun t => gamma t 0) := by fun_prop
  have hg1 : Measurable (fun t => gamma t 1) := by fun_prop
  have hlift (t : ℝ) (ht : t ∈ J) : e (gamma t) = target t := by
    rw [heq t ht, ← hF]
    exact F.right_inv ht
  have hbase (a : ℝ) (ha : a ∈ S) (t : ℝ)
      (hat : e !₂[a, height a] = target t) :
      t ∈ J ∧ gamma t = !₂[a, height a] := by
    have ht : t ∈ J := by
      change target t ∈ F.target
      rw [← hat, ← hF]
      exact F.map_source (hsource a ha)
    refine ⟨ht, ?_⟩
    rw [heq t ht]
    change F.symm (target t) = !₂[a, height a]
    rw [← hat, ← hF]
    exact F.left_inv (hsource a ha)
  let B := (T ∩ J) ∩ {t | gamma t 0 ∈ S} ∩
    {t | gamma t 1 = height (gamma t 0)}
  have hB : MeasurableSet B :=
    ((hT.inter hJ.measurableSet).inter (hS.preimage hg0)).inter
      (measurableSet_eq_fun hg1 (hh.comp hg0))
  have hBJ : B ⊆ J := fun _ ht => ht.1.1.2
  have hBT : B ⊆ T := fun _ ht => ht.1.1.1
  have hgraph (t : ℝ) (ht : t ∈ B) : gamma t 1 = height (gamma t 0) := ht.2
  have hrepr (t : ℝ) (ht : t ∈ B) : !₂[gamma t 0, height (gamma t 0)] = gamma t := by
    rw [← hgraph t ht]
    ext i
    fin_cases i <;> rfl
  have hBexact : B = m64IntrinsicCurveEndpointParameters e height S target T := by
    ext t
    constructor
    · intro ht
      refine ⟨hBT ht, gamma t 0, ht.1.2, ?_⟩
      rw [hrepr t ht]
      exact hlift t (hBJ ht)
    · rintro ⟨ht, a, ha, hat⟩
      obtain ⟨htJ, hgbase⟩ := hbase a ha t hat
      exact ⟨⟨⟨ht, htJ⟩, by simpa only [mem_ofPred_eq, hgbase, Matrix.cons_val_zero] using ha⟩,
        by simp only [mem_ofPred_eq, hgbase, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]⟩
  have himage : (fun t => gamma t 0) '' B = S := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ht.1.2
    · intro a ha
      obtain ⟨t, ht, hta⟩ := hend a ha
      obtain ⟨_, hgbase⟩ := hbase a ha t hta.symm
      refine ⟨t, ?_, ?_⟩
      · rw [hBexact]
        exact ⟨ht, a, ha, hta.symm⟩
      · simp only [hgbase, Matrix.cons_val_zero]
  have hlength := m64Intrinsic_lifted_curve_endpoint_graph_measure_le N hJ hg
    (fun t _ => he (gamma t)) hlift hB hBJ hBT htargetInj hgraph hc (by
      intro t ht v
      have h := hbound (gamma t 0) ht.1.2 v
      rw [hrepr t ht] at h
      exact h)
  rw [himage, hBexact] at hlength
  exact ⟨hBexact ▸ hB, hlength⟩

end PoincareConjecture
