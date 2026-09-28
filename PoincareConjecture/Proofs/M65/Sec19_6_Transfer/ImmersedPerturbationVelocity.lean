import PoincareConjecture.Proofs.M09.FamilyPhase
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

theorem angular_velocity_contMDiffOn
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U) :
    ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z,
        curveVelocity (n := 3) (fun x => c (z.1, (x, z.2.2))) z.2.1⟩ :
          TangentBundle (𝓡 3) M)) U := by
  let A : (P × ℝ) × ℝ → P × (ℝ × ℝ) := fun z => (z.1.1, (z.2, z.1.2))
  let B : P × (ℝ × ℝ) → (P × ℝ) × ℝ := fun z => ((z.1, z.2.2), z.2.1)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)
  have hB : ContDiff ℝ ∞ B :=
    (contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst
  have hf := hc.comp hA.contMDiff.contMDiffOn (fun _ hz => hz)
  have hp := (Proofs.M09.familyPhase_contMDiffOn (c ∘ A) (A ⁻¹' U)
    (hU.preimage hA.continuous) hf).comp hB.contMDiff.contMDiffOn
      (fun z hz => show A (B z) ∈ U from hz)
  simpa only [Proofs.M09.familyPhase, Proofs.M09.curvePhase, Function.comp_def,
    A, B, Prod.eta] using hp

theorem time_velocity_contMDiffOn
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U) :
    ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z,
        curveVelocity (n := 3) (fun t => c (z.1, (z.2.1, t))) z.2.2⟩ :
          TangentBundle (𝓡 3) M)) U := by
  let A : (P × ℝ) × ℝ → P × (ℝ × ℝ) := fun z => (z.1.1, (z.1.2, z.2))
  let B : P × (ℝ × ℝ) → (P × ℝ) × ℝ := fun z => ((z.1, z.2.1), z.2.2)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have hB : ContDiff ℝ ∞ B :=
    (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hf := hc.comp hA.contMDiff.contMDiffOn (fun _ hz => hz)
  have hp := (Proofs.M09.familyPhase_contMDiffOn (c ∘ A) (A ⁻¹' U)
    (hU.preimage hA.continuous) hf).comp hB.contMDiff.contMDiffOn
      (fun z hz => show A (B z) ∈ U from hz)
  simpa only [Proofs.M09.familyPhase, Proofs.M09.curvePhase, Function.comp_def,
    A, B, Prod.eta] using hp

end PoincareConjecture.M65Perturbation
