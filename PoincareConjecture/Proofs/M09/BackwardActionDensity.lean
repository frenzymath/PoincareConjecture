import PoincareConjecture.Proofs.M09.FamilyPhase
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Analysis.SpecialFunctions.Sqrt








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

set_option backward.isDefEq.respectTransparency false in
theorem backwardFamilyActionDensity_contDiffOn {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (hpositive : ∀ z ∈ U, 0 < z.2) (htime : ∀ z ∈ U, T - z.2 ∈ J) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ ↦
      backwardLIntegrand F T (fun s ↦ f (z.1, s)) z.2) U := by
  have hbase : ContMDiffOn (𝓘(ℝ, E × ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : E × ℝ ↦ (T - z.2, f z)) U :=
    (contDiff_const.sub contDiff_snd).contMDiff.contMDiffOn.prodMk hf
  have hg := F.smooth.comp hbase (fun z hz ↦ ⟨htime z hz, Set.mem_univ _⟩)
  have hphase := familyPhase_contMDiffOn f U hU hf
  have heval : ContMDiffOn (𝓘(ℝ, E × ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : E × ℝ ↦
        (⟨f z, (F.metric (T - z.2)).inner (f z)
          (curveVelocity (n := n) (fun s ↦ f (z.1, s)) z.2)
          (curveVelocity (n := n) (fun s ↦ f (z.1, s)) z.2)⟩ :
          Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ))) U :=
    hg.clm_bundle_apply₂ hphase hphase
  have henergy : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun z : E × ℝ ↦ (F.metric (T - z.2)).inner (f z)
        (curveVelocity (n := n) (fun s ↦ f (z.1, s)) z.2)
        (curveVelocity (n := n) (fun s ↦ f (z.1, s)) z.2)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval z hz)).2
  have hscalar := ((hM04.scalar_regular n M J F).comp hbase
    (fun z hz ↦ ⟨htime z hz, Set.mem_univ _⟩)).contDiffOn
  have hsqrt : ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ Real.sqrt z.2) U :=
    contDiff_snd.contDiffOn.sqrt (fun z hz ↦ (hpositive z hz).ne')
  exact hsqrt.mul (hscalar.add henergy.contDiffOn)

end PoincareConjecture.Proofs.M09
