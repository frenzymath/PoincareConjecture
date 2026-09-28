import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import PoincareConjecture.Statements.M63RampEstimates
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture

open Proofs.M58

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m63AngularFirstJet_eq_c1LoopTangent (gamma : C1FreeLoopSpace (M := M)) (x : ℝ) :
    m63AngularFirstJet (periodicFreeLoop gamma) x =
      c1LoopTangent gamma ⟨angularPoint x, norm_angularPoint x⟩ := by
  let z : LoopCircle := ⟨angularPoint x, norm_angularPoint x⟩
  have hg : MDifferentiableAt (𝓡 2) (𝓡 3) gamma.extension (angularPoint x) :=
    (contMDiffAt_loop_extension gamma.regularity z).mdifferentiableAt one_ne_zero
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) angularPoint x 1 = angularVector x := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      (hasDerivAt_angularPoint x).deriv
  have hv : curveVelocity (n := 3) (periodicFreeLoop gamma) x =
      mfderiv (𝓡 2) (𝓡 3) gamma.extension z.1 (loopCircleTangent z) := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (gamma.extension ∘ angularPoint) x 1 = _
    rw [mfderiv_comp_apply x hg (hasDerivAt_angularPoint x).differentiableAt.mdifferentiableAt,
      hd]
    rfl
  apply TotalSpace.ext (gamma.boundary z)
  exact heq_of_eq hv

theorem m63AngularFirstJet_continuous :
    Continuous (fun p : C1FreeLoopSpace (M := M) × ℝ =>
      m63AngularFirstJet (n := 3) (periodicFreeLoop p.1) p.2) := by
  have htheta : Continuous (fun x : ℝ =>
      (⟨angularPoint x, norm_angularPoint x⟩ : LoopCircle)) :=
    contDiff_angularPoint.continuous.subtype_mk _
  have h := (continuous_loop_tangent_eval (M := M)).comp
    (continuous_fst.prodMk (htheta.comp continuous_snd))
  convert h using 1
  funext p
  exact m63AngularFirstJet_eq_c1LoopTangent p.1 p.2

theorem m63FreeLoopLength_continuous (g : RiemannianMetric 3 M) :
    Continuous (freeLoopLength g) := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hv : Continuous (fun p : C1FreeLoopSpace (M := M) × ℝ =>
      (⟨periodicFreeLoop p.1 p.2, curveVelocity (periodicFreeLoop p.1) p.2⟩ :
        TangentBundle (𝓡 3) M)) := m63AngularFirstJet_continuous
  have hs : Continuous (fun p : C1FreeLoopSpace (M := M) × ℝ =>
      g.tangentNorm (periodicFreeLoop p.1 p.2)
        (curveVelocity (periodicFreeLoop p.1) p.2)) := (hv.inner_bundle hv).sqrt
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hs 0 rampPeriod

theorem m63FamilyLengthSup_properties (g : RiemannianMetric 3 M)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) :
    BddAbove (range (fun z => freeLoopLength g (Gamma z))) ∧
      (∃ z, freeLoopLength g (Gamma z) = m63FamilyLengthSup g Gamma) ∧
      0 ≤ m63FamilyLengthSup g Gamma ∧
      ∀ z, freeLoopLength g (Gamma z) ≤ m63FamilyLengthSup g Gamma := by
  let e : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  let : CompactSpace LoopTwoSphere := e.compactSpace
  let z0 : LoopTwoSphere := ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  have hcompact : IsCompact (range (fun z => freeLoopLength g (Gamma z))) :=
    isCompact_range ((m63FreeLoopLength_continuous g).comp Gamma.continuous)
  have hne : (range (fun z => freeLoopLength g (Gamma z))).Nonempty :=
    ⟨_, mem_range_self z0⟩
  have hsup : ∃ z, freeLoopLength g (Gamma z) = m63FamilyLengthSup g Gamma :=
    hcompact.sSup_mem hne
  have hle (z : LoopTwoSphere) : freeLoopLength g (Gamma z) ≤ m63FamilyLengthSup g Gamma :=
    le_csSup hcompact.bddAbove (mem_range_self z)
  exact ⟨hcompact.bddAbove, hsup, (freeLoopLength_nonneg g (Gamma z0)).trans (hle z0), hle⟩

end PoincareConjecture
