import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.CurveShortening.Deformation.Transfer.ImmersedPerturbation

/-!
# Genuine velocities of the perturbation family

The actual angular and time derivatives are jointly smooth bundled
fields in all perturbation variables. Both are instances of the proved
parameter-family tangent map, with the genuine variables permuted.
MT Lemma 19.4, pp. 439-441; M65 derivation 49, section 12.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace PoincareMT.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

/-- Joint smoothness of the actual angular velocity, retaining its
moving tangent base point. MT Lemma 19.4, pp. 439-441; derivation 49,
section 12. -/
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

/-- Joint smoothness of the actual time velocity in the same tangent
fiber as the angular velocity. MT Lemma 19.4, pp. 439-441; derivation 49,
section 12. -/
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

end PoincareMT.M65Perturbation
