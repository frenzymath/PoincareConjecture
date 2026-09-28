import PoincareConjecture.Proofs.M09.FamilyPhase
import PoincareConjecture.Proofs.M09.IntrinsicEnergy
import PoincareConjecture.Proofs.M09.SquareTimeFields

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def squareFamilyActionDensity {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (f : E × ℝ → M) (z : E × ℝ) : ℝ :=
  2 * z.2 ^ 2 * (F.connection (T - z.2 ^ 2)).scalarCurvature (f z) +
    (1 / 2 : ℝ) * regularizedCurveEnergy F T (fun s ↦ f (z.1, s)) z.2

set_option backward.isDefEq.respectTransparency false in
theorem squareFamilyActionDensity_contDiffOn {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (htime : ∀ z ∈ U, z.2 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    ContDiffOn ℝ ∞ (squareFamilyActionDensity F T f) U := by
  have hbase : ContMDiffOn (𝓘(ℝ, E × ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : E × ℝ ↦ (z.2, f z)) U :=
    contDiff_snd.contMDiff.contMDiffOn.prodMk hf
  have hg := (squareTime_metric_smooth F T b hb hwindow).comp hbase
    (fun z hz ↦ ⟨htime z hz, Set.mem_univ _⟩)
  have hphase := familyPhase_contMDiffOn f U hU hf
  have heval : ContMDiffOn (𝓘(ℝ, E × ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : E × ℝ ↦
        (⟨f z, regularizedCurveEnergy F T (fun s ↦ f (z.1, s)) z.2⟩ :
          Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ))) U :=
    hg.clm_bundle_apply₂ hphase hphase
  have henergy : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun z : E × ℝ ↦ regularizedCurveEnergy F T (fun s ↦ f (z.1, s)) z.2) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval z hz)).2
  have hscalar := ((squareTime_scalar_smooth F hM04 T b hb hwindow).comp hbase
    (fun z hz ↦ ⟨htime z hz, Set.mem_univ _⟩)).contDiffOn
  exact ((contDiffOn_const.mul (contDiff_snd.contDiffOn.pow 2)).mul hscalar).add
    (contDiffOn_const.mul henergy.contDiffOn)

end PoincareConjecture.Proofs.M09
