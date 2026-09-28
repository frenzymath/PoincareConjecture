import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationJets
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {J : Set ℝ}

theorem exists_chart_jet_control (F : RicciFlow 3 M (Icc a b)) (hJ : IsOpen J)
    (C : M65SmoothFilledLoopFamily F J)
    (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
    (delta : ℝ) (hdelta : 0 < delta)
    (hGamma : ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)))
    (hbase : ∀ q ∈ J, ∀ x, periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop (C.loops q) x)
    (q : M) (A : Set (ℝ × ℝ)) (hA : IsCompact A) (hAJ : A ⊆ univ ×ˢ J)
    (hchart : ∀ z ∈ A, periodicFreeLoop (C.loops z.2) z.1 ∈ (chartAt LoopAmbient q).source) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ delta ∧
      (∀ p ∈ ball 0 rho, ∀ z ∈ A,
        periodicFreeLoop (Gamma p z.2) z.1 ∈ (chartAt LoopAmbient q).source) ∧
      ∀ j : ℕ,
        TendstoUniformlyOn
          (fun p z => iteratedFDeriv ℝ j
            (fun w : ℝ × ℝ => (chartAt LoopAmbient q) (periodicFreeLoop (Gamma p w.2) w.1)) z)
          (iteratedFDeriv ℝ j
            (fun w : ℝ × ℝ => (chartAt LoopAmbient q) (periodicFreeLoop (C.loops w.2) w.1)))
          (𝓝 (0 : Fin N → ℝ)) A ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ ball 0 rho, ∀ z ∈ A,
          ‖iteratedFDeriv ℝ j
            (fun w : ℝ × ℝ =>
              (chartAt LoopAmbient q) (periodicFreeLoop (Gamma p w.2) w.1)) z‖ ≤ B := by
  let c := fun z : (Fin N → ℝ) × (ℝ × ℝ) => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1
  let e := chartAt LoopAmbient q
  let U : Set ((Fin N → ℝ) × (ℝ × ℝ)) := ball 0 delta ×ˢ (univ ×ˢ J)
  let W := U ∩ c ⁻¹' e.source
  have hU : IsOpen U := isOpen_ball.prod (isOpen_univ.prod hJ)
  have hW : IsOpen W := hGamma.continuousOn.isOpen_inter_preimage hU e.open_source
  have hzero (z : ℝ × ℝ) (hz : z ∈ A) : ((0 : Fin N → ℝ), z) ∈ W := by
    refine ⟨⟨mem_ball_self hdelta, hAJ hz⟩, ?_⟩
    change periodicFreeLoop (Gamma 0 z.2) z.1 ∈ e.source
    rw [hbase z.2 (hAJ hz).2 z.1]
    exact hchart z hz
  have hall : ∀ᶠ p in 𝓝 (0 : Fin N → ℝ), ∀ z ∈ A, (p, z) ∈ W :=
    hA.eventually_forall_of_forall_eventually (x₀ := 0)
      (P := fun p z => (p, z) ∈ W) (fun z hz => hW.mem_nhds (hzero z hz))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp hall
  let rho := min eta delta / 2
  have hrho : 0 < rho := div_pos (lt_min heta hdelta) (by norm_num)
  have hrhoeta : rho < eta := by dsimp only [rho]; have := min_le_left eta delta; linarith
  have hrhodelta : rho ≤ delta := by
    dsimp only [rho]
    have := min_le_right eta delta
    linarith
  have hcap : closedBall (0 : Fin N → ℝ) rho ×ˢ A ⊆ W := by
    intro z hz
    exact hball (mem_ball.mpr ((mem_closedBall.mp hz.1).trans_lt hrhoeta)) z.2 hz.2
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := contMDiffOn_chart
  have hf : ContDiffOn ℝ ∞ (fun z => e (c z)) W :=
    (he.comp (hGamma.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  refine ⟨rho, hrho, hrhodelta,
    fun p hp z hz => (hcap (show (p, z) ∈ closedBall 0 rho ×ˢ A from
      ⟨ball_subset_closedBall hp, hz⟩)).2, ?_⟩
  intro j
  have hjet := slice_jet_contDiffOn (fun z => e (c z)) W hW hf j
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hrestricted : ContinuousOn
      (fun z : (Fin N → ℝ) × A =>
        iteratedFDeriv ℝ j (fun w : ℝ × ℝ => e (c (z.1, w))) (z.2 : ℝ × ℝ))
      (ball 0 rho ×ˢ univ) :=
    hjet.continuousOn.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun z hz => hcap ⟨ball_subset_closedBall hz.1, z.2.property⟩)
  have hu : TendstoUniformlyOn
      (fun p z => iteratedFDeriv ℝ j (fun w : ℝ × ℝ => e (c (p, w))) z)
      (fun z => iteratedFDeriv ℝ j (fun w : ℝ × ℝ => e (c (0, w))) z)
      (𝓝 (0 : Fin N → ℝ)) A :=
    tendstoUniformlyOn_iff_restrict.mpr
      (hrestricted.tendstoUniformly (isOpen_ball.mem_nhds (mem_ball_self hrho)))
  refine ⟨hu.congr_right ?_, ?_⟩
  · intro z hz
    have heq : (fun w : ℝ × ℝ => e (c (0, w))) =ᶠ[𝓝 z]
        (fun w : ℝ × ℝ => e (periodicFreeLoop (C.loops w.2) w.1)) := by
      filter_upwards [(isOpen_univ.prod hJ).mem_nhds (hAJ hz)] with w hw
      exact congrArg e (hbase w.2 hw.2 w.1)
    exact (heq.iteratedFDeriv ℝ j).self_of_nhds
  · obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
      ((isCompact_closedBall (0 : Fin N → ℝ) rho).prod hA) (hjet.continuousOn.mono hcap)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro p hp z hz
    exact (hB (p, z) ⟨ball_subset_closedBall hp, hz⟩).trans (le_max_left _ _)

end PoincareConjecture.M65Perturbation
