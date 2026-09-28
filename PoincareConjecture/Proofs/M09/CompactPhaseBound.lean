import PoincareConjecture.Proofs.M09.FixedMetricSpeed
import PoincareConjecture.Proofs.M09.SpeedDistance
import PoincareConjecture.Proofs.M09.CompactTangentDisk
import PoincareConjecture.Proofs.M09.CurvePhase

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_uniform_compact_phase_bound {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (p : M) (b Emax : ℝ) (hb : 0 < b) (hbmax : b < τmax) (hEmax : 0 ≤ Emax) :
    ∃ K : Set (ℝ × TangentBundle (𝓡 n) M), IsCompact K ∧
      ∀ (γ : ℝ → M) (U : Set ℝ) (h : ℝ),
      0 ≤ h → h < Real.sqrt b → IsOpen U → Set.Icc 0 h ⊆ U →
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U → γ 0 = p →
      ∀ E : ParametricAlongCurveExtensionOn (n := n) (Set.Icc 0 h) γ
        (curveVelocityWithin (n := n) γ (Set.Icc 0 h)),
      (∀ s ∈ Set.Icc 0 h, regularizedLGeodesicEquation F T γ (Set.Icc 0 h) E s) →
      regularizedCurveEnergy F T γ 0 ≤ Emax →
      ∀ s ∈ Set.Icc 0 h, (s, curvePhase (n := n) γ s) ∈ K := by
  obtain ⟨C, hC, hspeed⟩ := exists_uniform_initialMetric_speed_bound F hM04 T τmax
    hτmax hwindow hcurvature b Emax hb hbmax hEmax
  let g := F.metric T
  letI : MetricSpace M := selectedMetricSpace g
  letI : ProperSpace M := selectedMetricSpace_proper g
    (hcurvature.1 T ⟨by linarith, le_rfl⟩)
  let B : Set M := Metric.closedBall p (C * Real.sqrt b)
  let D : Set (TangentBundle (𝓡 n) M) :=
    {z | z.proj ∈ B ∧ g.inner z.proj z.2 z.2 ≤ C ^ 2}
  have hDc : IsCompact D := isCompact_tangentDisk g B (isCompact_closedBall _ _)
    (C ^ 2) (sq_nonneg C)
  refine ⟨Set.Icc 0 (Real.sqrt b) ×ˢ D, isCompact_Icc.prod hDc, ?_⟩
  intro γ U h hh hhb hU hIU hγ hstart E heq hE s hs
  have hv := hspeed γ U h hh hhb hU hIU hγ E heq hE
  have hsub : Set.Icc 0 s ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl hs.2
  have hdist := selectedMetric_dist_le_of_speed_le g γ 0 s C hs.1 hC.le
    ((hγ.of_le (by simp)).mono (hsub.trans hIU)) (fun t ht ↦ hv t (hsub ht))
  have hsqrt : s ≤ Real.sqrt b := hs.2.trans hhb.le
  have hbase : γ s ∈ B := by
    change dist (γ s) p ≤ C * Real.sqrt b
    rw [dist_comm, ← hstart]
    exact hdist.trans (by simpa only [sub_zero] using mul_le_mul_of_nonneg_left hsqrt hC.le)
  have hnonneg : 0 ≤ g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s) := by
    rcases eq_or_ne (curveVelocity (n := n) γ s) 0 with hz | hz
    · simp [hz]
    · exact (g.pos (γ s) (curveVelocity γ s) hz).le
  have hsquare : (g.tangentNorm (γ s) (curveVelocity γ s)) ^ 2 =
      g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s) := Real.sq_sqrt hnonneg
  have hquadratic : g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s) ≤ C ^ 2 := by
    have hnorm := hv s hs
    have hn : 0 ≤ g.tangentNorm (γ s) (curveVelocity γ s) := Real.sqrt_nonneg _
    nlinarith
  exact ⟨⟨hs.1, hsqrt⟩, hbase, hquadratic⟩

end PoincareConjecture.Proofs.M09
