import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak



theorem m64WeakPartial_comp_linear {m k : ℕ} {O : Set LoopPlane}
    {u W : LoopPlane → EuclideanSpace ℝ (Fin m)} {i : Fin 2}
    (hu : MemLp u 2 (volume.restrict O))
    (hW : MemLp W 2 (volume.restrict O))
    (hw : ∀ b, HasWeakPartialDeriv i (fun p => W p b) (fun p => u p b) O)
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) (a : Fin k) :
    HasWeakPartialDeriv i (fun p => L (W p) a) (fun p => L (u p) a) O := by
  intro phi hphi hc hs
  let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hp : MemLp phi 2 (volume.restrict O) :=
    (hphi.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdp : MemLp dphi 2 (volume.restrict O) :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  have hintu := m64L2_test_integrable hu hdp
  have hintW := m64L2_test_integrable hW hp
  have hvec : (∫ p in O, dphi p • u p) = -(∫ p in O, phi p • W p) := by
    ext b
    change (EuclideanSpace.proj (𝕜 := ℝ) b) (∫ p in O, dphi p • u p) =
      (EuclideanSpace.proj (𝕜 := ℝ) b) (-(∫ p in O, phi p • W p))
    rw [map_neg, ← (EuclideanSpace.proj (𝕜 := ℝ) b).integral_comp_comm hintu,
      ← (EuclideanSpace.proj (𝕜 := ℝ) b).integral_comp_comm hintW]
    simpa only [EuclideanSpace.coe_proj, PiLp.smul_apply, smul_eq_mul, mul_comm,
      dphi] using hw b phi hphi hc hs
  let T := (EuclideanSpace.proj (𝕜 := ℝ) a).comp L
  have h := congrArg T hvec
  rw [map_neg, ← T.integral_comp_comm hintu, ← T.integral_comp_comm hintW] at h
  simpa only [T, ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj,
    map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm, dphi] using h

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "S" => interior m64AnnulusDomain

omit [IsManifold (𝓡 n) ∞ M] in


theorem M64ObservedWeakAnnulus.exists_local_chart_columns
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : Continuous e) (hread : M60.SUChartReadable (n := n) e)
    (hA : ContinuousOn A.map S) {a : LoopPlane} (ha : a ∈ S) :
    ∃ (b : M) (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (R : ℝ), 0 < R ∧ Metric.closedBall a R ⊆ S ∧
      (∀ p ∈ Metric.closedBall a R,
        A.map p ∈ (extChartAt (𝓡 n) b).source ∧
          L (e (A.map p)) = extChartAt (𝓡 n) b (A.map p)) ∧
      ContinuousOn (fun p => L (e (A.map p))) (Metric.closedBall a R) ∧
      MemLp (fun p => L (e (A.map p))) 2 (volume.restrict (Metric.ball a R)) ∧
      (∀ i, MemLp (fun p => L (A.column i p)) 2 (volume.restrict (Metric.ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i (fun p => L (A.column i p) j)
        (fun p => L (e (A.map p)) j) (Metric.ball a R) := by
  obtain ⟨b, hb, L, hL⟩ := hread (A.map a)
  have hAa : ContinuousAt A.map a := hA.continuousAt (isOpen_interior.mem_nhds ha)
  have hnear : {p | A.map p ∈ (extChartAt (𝓡 n) b).source ∧
      L (e (A.map p)) = extChartAt (𝓡 n) b (A.map p)} ∈ 𝓝 a := by
    exact inter_mem
      (hAa.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb))
      (hL.comp_tendsto hAa)
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (isOpen_interior.mem_nhds ha) hnear)
  have hRS : Metric.closedBall a R ⊆ S := fun p hp => (hball hp).1
  have hBS : Metric.ball a R ⊆ S := Metric.ball_subset_closedBall.trans hRS
  refine ⟨b, L, R, hR, hRS, (fun p hp => (hball hp).2), ?_, ?_, ?_, ?_⟩
  · exact (L.continuous.comp_continuousOn (he.comp_continuousOn hA)).mono hRS
  · exact (L.comp_memLp' A.observed_memLp).mono_measure (Measure.restrict_mono hBS le_rfl)
  · intro i
    exact (L.comp_memLp' (Lp.memLp (A.column i))).mono_measure
      (Measure.restrict_mono hBS le_rfl)
  · intro i j
    exact (m64WeakPartial_comp_linear A.observed_memLp (Lp.memLp (A.column i))
      (A.weak_partial i) L j).restrict Metric.isOpen_ball hBS

end PoincareConjecture
