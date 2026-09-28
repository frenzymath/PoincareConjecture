import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BoundaryMotionTrace
import PoincareConjecture.Proofs.M09.CurvePhase
import Mathlib.Analysis.Calculus.TangentCone.Real











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture



theorem m65LoopDisk_uniqueMDiffOn : UniqueMDiffOn (𝓡 2) loopDiskSet := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex (convex_closedBall (0 : LoopPlane) 1)
  rw [interior_closedBall _ one_ne_zero]
  exact Metric.nonempty_ball.mpr zero_lt_one

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m65BoundaryColumnTrace_eq_mfderivWithin
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f loopDiskSet)
    (V : (z : LoopPlane) → TangentSpace (𝓡 n) (f z)) (v : LoopPlane)
    (hV : ContinuousOn (fun z => (⟨f z, V z⟩ : TangentBundle (𝓡 n) M)) loopDiskSet)
    (hVi : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, V z = mfderiv (𝓡 2) (𝓡 n) f z v)
    {z : LoopPlane} (hz : z ∈ loopDiskSet) :
    V z = mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z v := by
  let : T2Space (TangentBundle (𝓡 n) M) := Proofs.M09.tangentBundle_t2Space
  have hD : ContinuousOn (fun z => (⟨f z,
      mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z v⟩ : TangentBundle (𝓡 n) M))
      loopDiskSet :=
    (hf.continuousOn_tangentMapWithin le_rfl m65LoopDisk_uniqueMDiffOn).comp
      (((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn) (fun _ hw => hw)
  have heq : EqOn (fun z => (⟨f z, V z⟩ : TangentBundle (𝓡 n) M))
      (fun z => (⟨f z, mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet z v⟩ :
        TangentBundle (𝓡 n) M)) (Metric.ball (0 : LoopPlane) 1) := by
    intro w hw
    have hv : V w = mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet w v := by
      have hmem : loopDiskSet ∈ 𝓝 w :=
        mem_of_superset (Metric.isOpen_ball.mem_nhds hw) Metric.ball_subset_closedBall
      have hd : mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet w =
          mfderiv (𝓡 2) (𝓡 n) f w := mfderivWithin_of_mem_nhds hmem
      exact (hVi w hw).trans (congrArg (fun L : TangentSpace (𝓡 2) w →L[ℝ]
        TangentSpace (𝓡 n) (f w) => L v) hd).symm
    exact congrArg (fun a : TangentSpace (𝓡 n) (f w) =>
      (⟨f w, a⟩ : TangentBundle (𝓡 n) M)) hv
  have hall := heq.of_subset_closure hV hD Metric.ball_subset_closedBall (by
    rw [closure_ball (0 : LoopPlane) one_ne_zero]
    exact Subset.rfl)
  exact congrArg (fun q : TangentBundle (𝓡 n) M =>
    (show EuclideanSpace ℝ (Fin n) from q.2)) (hall hz)




theorem m65BoundaryCurve_velocity_of_trace
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f loopDiskSet)
    (E : (z : LoopPlane) → Fin 2 → TangentSpace (𝓡 n) (f z))
    (hE : ∀ i, ContinuousOn (fun z => (⟨f z, E z i⟩ : TangentBundle (𝓡 n) M)) loopDiskSet)
    (hEi : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ∀ i,
      E z i = mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 (f ∘ Proofs.M58.angularPoint) ∧
      ∀ θ : ℝ, curveVelocity (f ∘ Proofs.M58.angularPoint) θ =
        ∑ i : Fin 2, (Proofs.M58.angularVector θ) i • E (Proofs.M58.angularPoint θ) i := by
  have hcircle (θ : ℝ) : Proofs.M58.angularPoint θ ∈ loopDiskSet := by
    simp only [loopDiskSet, mem_closedBall_zero_iff, Proofs.M58.norm_angularPoint, le_refl]
  have hc : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 2) 1 Proofs.M58.angularPoint :=
    (Proofs.M58.contDiff_angularPoint.of_le (by simp)).contMDiff
  refine ⟨contMDiffOn_univ.mp (hf.comp hc.contMDiffOn (fun θ _ => hcircle θ)), ?_⟩
  intro θ
  have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (I'' := 𝓡 n) θ
    ((hf _ (hcircle θ)).mdifferentiableWithinAt (by decide))
    ((hc θ).mdifferentiableAt (by decide)).mdifferentiableWithinAt
    (show univ ⊆ Proofs.M58.angularPoint ⁻¹' loopDiskSet from fun s _ => hcircle s)
    (uniqueMDiffWithinAt_univ (𝓘(ℝ, ℝ)))
  simp only [mfderivWithin_univ] at hchain
  have hvelocity : mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) Proofs.M58.angularPoint θ 1 =
      Proofs.M58.angularVector θ := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      (Proofs.M58.hasDerivAt_angularPoint θ).deriv
  change mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (f ∘ Proofs.M58.angularPoint) θ 1 = _
  rw [hchain]
  change mfderivWithin (𝓡 2) (𝓡 n) f loopDiskSet (Proofs.M58.angularPoint θ)
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) Proofs.M58.angularPoint θ 1) = _
  rw [hvelocity]
  have hv : Proofs.M58.angularVector θ = ∑ i : Fin 2,
      (Proofs.M58.angularVector θ) i • EuclideanSpace.basisFun (Fin 2) ℝ i := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_two, EuclideanSpace.single]
  nth_rw 1 [hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, ← m65BoundaryColumnTrace_eq_mfderivWithin f hf (fun z => E z i)
    (EuclideanSpace.basisFun (Fin 2) ℝ i) (hE i) (fun z hz => hEi z hz i) (hcircle θ)]

end PoincareConjecture
