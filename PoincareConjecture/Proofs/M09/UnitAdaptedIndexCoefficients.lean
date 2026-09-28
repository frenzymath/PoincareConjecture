import PoincareConjecture.Proofs.M09.SmoothIndexDensity
import PoincareConjecture.Proofs.M09.CompactVelocityExtension
import PoincareConjecture.Proofs.M09.CompactDerivativeExtension
import PoincareConjecture.Proofs.M09.ScaledAdaptedField
import PoincareConjecture.Proofs.M09.FiniteFieldSum

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem unit_index_cross_coefficient {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (q : M) (s : ℝ) (a v w : TangentSpace (𝓡 n) q)
    (hv : (F.metric (T - s ^ 2)).inner q v v = 1) :
    pointwiseSecondVariationDensity F T q s a v (v + w) -
      pointwiseSecondVariationDensity F T q s a v w - 1 =
        2 * (F.metric (T - s ^ 2)).inner q v w := by
  dsimp only [pointwiseSecondVariationDensity]
  simp only [map_add, add_apply, hv, (F.metric (T - s ^ 2)).symm q w v]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseSecondVariationDensity_unit_scaled {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (q : M) (s : ℝ)
    (hs : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (a v w : TangentSpace (𝓡 n) q) (f fp : ℝ)
    (hv : (F.metric (T - s ^ 2)).inner q v v = 1) :
    pointwiseSecondVariationDensity F T q s a (f • v) (fp • v + f • w) =
      fp ^ 2 + (2 * (F.metric (T - s ^ 2)).inner q v w) * f * fp +
        pointwiseSecondVariationDensity F T q s a v w * f ^ 2 := by
  let D := F.connection (T - s ^ 2)
  obtain ⟨H, hH⟩ := squareTime_hessian_exists_bilinear F T τmax hτmax hwindow q s hs
    D.scalarCurvature (scalarCurvature_contMDiff hM04 D).contMDiffOn
  have hHscale : D.hessian D.scalarCurvature q (f • v) (f • v) =
      f ^ 2 * D.hessian D.scalarCurvature q v v := by
    rw [hH, hH]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  dsimp only [pointwiseSecondVariationDensity]
  rw [curvature_index_smul hM04 D, ricciDerivative_smul_first_third hM04 D,
    ricciDerivative_smul_last_two hM04 D, hHscale]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, hv,
    (F.metric (T - s ^ 2)).symm q w v]
  ring

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_unit_adapted_scalar_coefficients {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (α : ℝ → M) (P : ∀ s, TangentSpace (𝓡 n) (α s)) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hP : IsAdaptedFieldOn F T α P U)
    (hunit : ∀ s ∈ U, (F.metric (T - s ^ 2)).inner (α s) (P s) (P s) = 1) :
    ∃ (V : Set ℝ) (B C : ℝ → ℝ), IsOpen V ∧ Set.Icc 0 c ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ B V ∧ ContDiffOn ℝ ∞ C V ∧
      ∀ s ∈ Set.Icc 0 c,
        B s = -4 * s * (F.connection (T - s ^ 2)).ricci (α s) (P s) (P s) ∧
        ∀ f fp : ℝ,
          pointwiseSecondVariationDensity F T (α s) s (curveVelocity α s) (f • P s)
            (fp • P s - (2 * s * f) •
              ricciOperator hM04 (F.connection (T - s ^ 2)) (α s) (P s)) =
            fp ^ 2 + B s * f * fp + C s * f ^ 2 := by
  let K := Set.Icc 0 c
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc hc
  obtain ⟨HP⟩ := nonempty_parametricFieldExtensionOn_compact α P U K hU hKU
    isCompact_Icc hα hP.smooth
  obtain ⟨HA⟩ := nonempty_velocityExtensionOn_compact α U K hU hKU isCompact_Icc hKd hα
  obtain ⟨HW⟩ := nonempty_pullbackDerivativeExtensionOn_compact F T τmax hτmax hwindow
    α P U K hU hKU isCompact_Icc hKd (hKU.trans htime) hα HP
  let g : ℝ → ℝ × M := fun s ↦ (s, α s)
  have hg : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞ g U :=
    contMDiffOn_id.prodMk hα
  let V := U ∩ g ⁻¹' (HA.domain ∩ HW.domain)
  have hV : IsOpen V := hg.continuousOn.isOpen_inter_preimage hU
    (HA.open_domain.inter HW.open_domain)
  have hKV : K ⊆ V := fun s hs ↦ ⟨hKU hs, HA.graph_mem s hs, HW.graph_mem s hs⟩
  have hαV := hα.mono (show V ⊆ U from Set.inter_subset_left)
  have hgV := hg.mono (show V ⊆ U from Set.inter_subset_left)
  let A0 : ∀ s, TangentSpace (𝓡 n) (α s) := fun s ↦ HA.extension s (α s)
  let W : ∀ s, TangentSpace (𝓡 n) (α s) := fun s ↦ HW.extension s (α s)
  have hA0 : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, A0 s⟩ : TangentBundle (𝓡 n) M)) V :=
    HA.smooth.comp hgV (fun _ hs ↦ hs.2.1)
  have hW : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, W s⟩ : TangentBundle (𝓡 n) M)) V :=
    HW.smooth.comp hgV (fun _ hs ↦ hs.2.2)
  have hPV := hP.smooth.mono (show V ⊆ U from Set.inter_subset_left)
  have hPW : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, P s + W s⟩ : TangentBundle (𝓡 n) M)) V := by
    have hsum := field_sum_smooth α (fun i : Fin 2 ↦ ![P, W] i) V hV hαV (by
      intro i
      fin_cases i
      · exact hPV
      · exact hW)
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hsum
  let C : ℝ → ℝ := fun s ↦ pointwiseSecondVariationDensity F T (α s) s (A0 s) (P s) (W s)
  let C1 : ℝ → ℝ := fun s ↦
    pointwiseSecondVariationDensity F T (α s) s (A0 s) (P s) (P s + W s)
  let B : ℝ → ℝ := fun s ↦ C1 s - C s - 1
  have hC := pointwiseSecondVariationDensity_contDiffOn F hM04 T τmax hτmax hwindow
    α A0 P W V hV (fun _ hs ↦ htime hs.1) hαV hA0 hPV hW
  have hC1 := pointwiseSecondVariationDensity_contDiffOn F hM04 T τmax hτmax hwindow
    α A0 P (fun s ↦ P s + W s) V hV (fun _ hs ↦ htime hs.1) hαV hA0 hPV hPW
  refine ⟨V, B, C, hV, hKV, Set.inter_subset_left, (hC1.sub hC).sub contDiffOn_const, hC, ?_⟩
  intro s hs
  have hAeq : A0 s = curveVelocity α s := (HA.agrees s hs).trans
    (curveVelocityWithin_eq_curveVelocity α K s (hKd s hs)
      ((hα.contMDiffAt (hU.mem_nhds (hKU hs))).mdifferentiableAt (by simp)))
  have hWeq : W s = -(2 * s) •
      ricciOperator hM04 (F.connection (T - s ^ 2)) (α s) (P s) :=
    (HW.agrees s hs).trans (IsAdaptedFieldOn.pullback_eq_ricciOperator F hM04 T τmax
      hτmax hwindow α P K U hU hα hP HP s hs (hKU hs) (hKd s hs) (htime (hKU hs)))
  have hBcross : B s = 2 * (F.metric (T - s ^ 2)).inner (α s) (P s) (W s) :=
    unit_index_cross_coefficient F T (α s) s (A0 s) (P s) (W s) (hunit s (hKU hs))
  refine ⟨?_, ?_⟩
  · rw [hBcross, hWeq]
    simp only [map_smul, smul_apply, smul_eq_mul,
      (F.metric (T - s ^ 2)).symm (α s) (P s) _, ricciOperator_pairing]
    ring
  · intro f fp
    have h := pointwiseSecondVariationDensity_unit_scaled F hM04 T τmax hτmax hwindow
      (α s) s (htime (hKU hs)) (A0 s) (P s) (W s) f fp (hunit s (hKU hs))
    rw [← hBcross] at h
    change _ = fp ^ 2 + B s * f * fp + C s * f ^ 2 at h
    rw [hAeq, hWeq, smul_smul,
      show f * -(2 * s) = -(2 * s * f) by ring, neg_smul, ← sub_eq_add_neg] at h
    exact h

end PoincareConjecture.Proofs.M09
