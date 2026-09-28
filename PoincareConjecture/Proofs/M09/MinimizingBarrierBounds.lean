import PoincareConjecture.Proofs.M09.ParametricComparisonAction
import PoincareConjecture.Proofs.M09.LocalParametricBounds

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => TangentSpace (𝓡 n) p × ℝ

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_local_minimizing_barrier_bounds
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z0 : TangentSpace (𝓡 n) p)
    (b0 : ℝ) (hb0 : 0 < b0) (hmax0 : b0 < τmax) :
    ∃ N : Set P, IsOpen N ∧ (Z0, b0) ∈ N ∧ N ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ a ∈ N, ∀ (ha : 0 < a.2) (hm : a.2 < τmax),
        IsMinimizingBackwardLPath F T 0 a.2 (A.path a.1 a.2 ha hm) →
        ∃ B : ReducedLengthUpperBarrier F T p (A.gamma a.1 a.2) a.2,
          |deriv (fun s ↦ B.representative (A.gamma a.1 a.2, s)) a.2| ≤ D ∧
          reducedLengthGradientNormSq F T B.representative a.2 (A.gamma a.1 a.2) ≤ D ∧
          ∀ v : TangentSpace (𝓡 n) (A.gamma a.1 a.2),
            (F.connection (T - a.2)).hessian (fun q ↦ B.representative (q, a.2))
              (A.gamma a.1 a.2) v v ≤ D * (F.metric (T - a.2)).inner (A.gamma a.1 a.2) v v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let e := chartAt E (A.gamma Z0 b0)
  obtain ⟨W, V, C, hW, haW, hWt, hV, hVe, hC, hcenters⟩ :=
    lExponentialFamily_exists_parametric_comparison_action hM04 hL hτmax hwindow A Z0 b0 hb0 hmax0
  let Ψ : P → (P × E) × ℝ := fun a ↦ ((a, e (A.gamma a.1 a.2)), a.2)
  have hcenter := hcenters (Z0, b0) haW
  obtain ⟨U, hU, hzU, hUsub, D, hD, hbound⟩ := exists_local_parametric_derivative_bounds
    F T τmax hτmax hwindow (A.gamma Z0 b0) C (V ×ˢ Set.Ioo 0 τmax)
      (hV.prod isOpen_Ioo) hC (Ψ (Z0, b0)) ⟨hcenter.2.1, hb0, hmax0⟩
        (e.map_source hcenter.1) hb0 hmax0
  have hγ : ContMDiffOn (𝓘(ℝ, P)) (𝓡 n) ∞ (fun a : P ↦ A.gamma a.1 a.2) W := by
    convert! A.gamma_smooth.mono hWt using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have heγ : ContDiffOn ℝ ∞ (fun a : P ↦ e (A.gamma a.1 a.2)) W :=
    (contMDiffOn_chart.comp hγ (fun a ha ↦ (hcenters a ha).1)).contDiffOn
  have hΨ : ContinuousOn Ψ W :=
    ((contDiffOn_id.prodMk heγ).prodMk contDiff_snd.contDiffOn).continuousOn
  let N := W ∩ Ψ ⁻¹' U
  have hN : IsOpen N := hΨ.isOpen_inter_preimage hW hU
  refine ⟨N, hN, ⟨haW, hzU⟩, fun a ha ↦ hWt ha.1, D, hD, ?_⟩
  intro a ha hat hmax hmin
  obtain ⟨B, hB⟩ := (hcenters a ha.1).2.2 hat hmax hmin
  have h := hbound (Ψ a) ha.2
  have hsource := (hcenters a ha.1).1
  dsimp only [Ψ, e] at h
  change _ ∧ _ ∧ ∀ v : E, _ at h
  rw [(chartAt E (A.gamma Z0 b0)).left_inv hsource] at h
  refine ⟨B, ?_⟩
  rw [hB]
  exact h

end PoincareConjecture.Proofs.M09
