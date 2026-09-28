import PoincareConjecture.Proofs.M09.FamilyActionDensity
import PoincareConjecture.Proofs.M09.SquareActionIntegral

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem smoothSquareCurve_scalar_energy {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (α : ℝ → M) (D : Set ℝ) (hD : IsOpen D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (htime : D ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)) :
    ContDiffOn ℝ ∞ (fun s ↦ (F.connection (T - s ^ 2)).scalarCurvature (α s)) D ∧
      ContDiffOn ℝ ∞ (regularizedCurveEnergy F T α) D := by
  have hbase : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun s ↦ (s, α s)) D := contMDiffOn_id.prodMk hα
  have hg := (squareTime_metric_smooth F T τmax hτmax hwindow).comp hbase
    (fun s hs ↦ ⟨htime hs, Set.mem_univ _⟩)
  have hphase := curvePhase_contMDiffOn α D hD hα
  have heval : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun s ↦ (⟨α s, regularizedCurveEnergy F T α s⟩ :
        Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ))) D :=
    hg.clm_bundle_apply₂ hphase hphase
  have henergy : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (regularizedCurveEnergy F T α) D := by
    intro s hs
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval s hs)).2
  exact ⟨((squareTime_scalar_smooth F hM04 T τmax hτmax hwindow).comp hbase
    (fun s hs ↦ ⟨htime hs, Set.mem_univ _⟩)).contDiffOn, henergy.contDiffOn⟩

theorem exists_backwardPath_of_smoothSquareCurve {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (α : ℝ → M) (D : Set ℝ) (hD : IsOpen D)
    (hI : Set.Icc 0 (Real.sqrt b) ⊆ D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D) :
    ∃ P : BackwardTimePath F T 0 b,
      P.curve = (fun τ ↦ α (Real.sqrt τ)) ∧
      backwardLLength F T 0 b P.curve =
        ∫ s in 0..Real.sqrt b,
          2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
            (1 / 2 : ℝ) * regularizedCurveEnergy F T α s := by
  let U := D ∩ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hU : IsOpen U := hD.inter isOpen_Ioo
  have hIU : Set.Icc 0 (Real.sqrt b) ⊆ U := by
    intro s hs
    exact ⟨hI hs, (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hαU := hα.mono (show U ⊆ D from Set.inter_subset_left)
  obtain ⟨hR, hE⟩ := smoothSquareCurve_scalar_energy F hM04 T τmax hτmax hwindow
    α U hU hαU Set.inter_subset_right
  have hαd : ∀ s ∈ Set.Ioo 0 (Real.sqrt b),
      MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s := by
    intro s hs
    exact (hαU.contMDiffAt (hU.mem_nhds (hIU (Set.Ioo_subset_Icc_self hs)))).mdifferentiableAt
      (by simp)
  have hi := intervalIntegrable_backwardLIntegrand_comp_sqrt F T b hb α hαd
    (hR.continuousOn.mono hIU) (hE.continuousOn.mono hIU)
  have hmap : Set.MapsTo Real.sqrt (Set.Icc 0 b) U := by
    intro τ hτ
    exact hIU ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hτ.2⟩
  have hsqrt : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.sqrt (Set.Ioo 0 b) := by
    intro τ hτ
    exact (Real.contDiffAt_sqrt hτ.1.ne').contMDiffAt.contMDiffWithinAt
  let P : BackwardTimePath F T 0 b := {
    curve := fun τ ↦ α (Real.sqrt τ)
    nonnegative := le_rfl
    ordered := hb
    terminal_mem := hwindow ⟨by linarith, le_rfl⟩
    time_mem := fun τ hτ ↦ hwindow ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    continuous := hαU.continuousOn.comp Real.continuous_sqrt.continuousOn hmap
    regular := (hαU.comp hsqrt (fun τ hτ ↦ hmap (Set.Ioo_subset_Icc_self hτ))).of_le (by simp)
    l_integrable := hi
  }
  exact ⟨P, rfl, backwardLLength_comp_sqrt_eq F T b hb α hαd⟩

end PoincareConjecture.Proofs.M09
