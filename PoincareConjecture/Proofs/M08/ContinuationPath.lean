import PoincareConjecture.Proofs.M08.ContinuationZero
import PoincareConjecture.Proofs.M08.ContinuationRegularized
import PoincareConjecture.Proofs.M08.RegularizedGeodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

set_option maxHeartbeats 1400000 in
theorem exists_extended_square_continuation {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 < τ₁) (hτ₂ : τ₂ ≤ τmax)
    (p : BackwardTimePath F T τ₁ τ₂) (R : RegularizedLGeodesicData p) :
    ∃ α : ℝ → M,
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc 0 (Real.sqrt τ₂)) ∧
      IsContinuationCurve F T α (Ioo 0 (Real.sqrt τ₂)) ∧
      EqOn α R.path.curve (sqrtParameterInterval τ₁ τ₂) := by
  classical
  let A := Real.sqrt τ₁
  let B := Real.sqrt τ₂
  have hA : 0 < A := Real.sqrt_pos.mpr hτ₁
  have hAB : A < B := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have hB : 0 < B := hA.trans hAB
  obtain ⟨c, hAc, hcB⟩ := exists_between hAB
  obtain ⟨b, hcb, hbB⟩ := exists_between hcB
  have hc : 0 < c := hA.trans hAc
  have hb : 0 < b := hc.trans hcb
  have hcm : c ^ 2 < τmax := by
    have hsq := (sq_lt_sq₀ hc.le hB.le).mpr hcB
    have hBsq : B ^ 2 = τ₂ := Real.sq_sqrt (hτ₁.trans p.ordered).le
    rw [hBsq] at hsq
    exact hsq.trans_le hτ₂
  have htimeB (s : ℝ) (hs : s ∈ Ioo 0 B) : T - s ^ 2 ∈ interior J := by
    apply backwardSquareTime_mem_interior hwindow (τ₁ := 0) le_rfl
      (hτ₁.trans p.ordered) hτ₂
    simpa only [Real.sqrt_zero, B] using hs
  have hR : IsContinuationCurve F T R.path.curve (Ioo A B) :=
    regularizedData_isContinuationCurve hM04 hwindow hτ₂ p R
  obtain ⟨β, hβ, hβ0, hβtail⟩ := exists_continuation_to_zero F hM04 T τmax hA.le hAc
    hcb hcm hwindow hcurvature (fun s hs ↦ htimeB s ⟨hs.1, hs.2.trans hbB⟩)
    R.path.curve (hR.mono (Ioo_subset_Ioo le_rfl hbB.le))
  have hβR : EqOn β R.path.curve (Ioo A b) := by
    have h := continuationCurve_eqOn_of_tail F hM04 T (d := 0) (e := A)
      le_rfl hA.le hc hAc hcb (fun s hs ↦ interior_subset (htimeB s ⟨hs.1, hs.2.trans hbB⟩))
      hβ (hR.mono (Ioo_subset_Ioo le_rfl hbB.le)) hβtail (fun _ _ ↦ rfl)
    simpa only [max_eq_right hA.le] using h
  let t := (c + b) / 2
  have hct : c < t := by dsimp only [t]; linarith
  have htb : t < b := by dsimp only [t]; linarith
  let α : ℝ → M := fun s ↦ if s ≤ t then β s else R.path.curve s
  have hαβ : EqOn α β (Iio b) := by
    intro s hs
    dsimp only [α]
    split_ifs with hst
    · rfl
    · exact (hβtail ⟨hct.trans (lt_of_not_ge hst), hs⟩).symm
  have hαR : EqOn α R.path.curve (Ioi c) := by
    intro s hs
    dsimp only [α]
    split_ifs with hst
    · exact hβtail ⟨hs, hst.trans_lt htb⟩
    · rfl
  have hαL : IsContinuationCurve F T α (Ioo 0 b) :=
    hβ.congr isOpen_Ioo (fun s hs ↦ hαβ hs.2)
  have hαU : IsContinuationCurve F T α (Ioo c B) :=
    (hR.mono (Ioo_subset_Ioo hAc.le le_rfl)).congr isOpen_Ioo (fun s hs ↦ hαR hs.1)
  have hαI : IsContinuationCurve F T α (Ioo 0 B) := by
    apply (hαL.union isOpen_Ioo isOpen_Ioo hαU).mono
    intro s hs
    by_cases hsb : s < b
    · exact Or.inl ⟨hs.1, hsb⟩
    · exact Or.inr ⟨hcb.trans_le (le_of_not_gt hsb), hs.2⟩
  have hαC : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc 0 B) := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      have hnear : α =ᶠ[𝓝 (0 : ℝ)] β := eventuallyEq_of_mem (Iio_mem_nhds hb) hαβ
      exact (hβ0.congr_of_eventuallyEq (hnear.filter_mono nhdsWithin_le_nhds)
        hnear.self_of_nhds).mono Icc_subset_Ici_self
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      rcases eq_or_lt_of_le hs.2 with hseq | hsB
      · subst s
        have hBC : B ∈ sqrtParameterInterval τ₁ τ₂ := ⟨hAB.le, le_rfl⟩
        exact (((R.path.smooth B (R.path.interval_subset hBC)).contMDiffAt
          (R.path.open_domain.mem_nhds (R.path.interval_subset hBC))).congr_of_eventuallyEq
          (eventuallyEq_of_mem (Ioi_mem_nhds hcB) hαR)).contMDiffWithinAt
      · exact ((hαI.smooth s ⟨hspos, hsB⟩).contMDiffAt
          (isOpen_Ioo.mem_nhds ⟨hspos, hsB⟩)).contMDiffWithinAt
  have hαRo : EqOn α R.path.curve (Ioo A B) := by
    intro s hs
    by_cases hsb : s < b
    · exact (hαβ hsb).trans (hβR ⟨hs.1, hsb⟩)
    · exact hαR (hcb.trans_le (le_of_not_gt hsb))
  have hαRc : EqOn α R.path.curve (Icc A B) := hαRo.of_subset_closure
    (hαC.continuousOn.mono (Icc_subset_Icc hA.le le_rfl))
    (R.path.smooth.continuousOn.mono R.path.interval_subset) Ioo_subset_Icc_self
    (by rw [closure_Ioo hAB.ne])
  exact ⟨α, hαC, hαI, hαRc⟩

end PoincareConjecture.M08
