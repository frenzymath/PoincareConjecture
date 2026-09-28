import PoincareConjecture.Proofs.M09.CurvePhase
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def familyPhase (f : E × ℝ → M) (z : E × ℝ) : TangentBundle (𝓡 n) M :=
  curvePhase (n := n) (fun s ↦ f (z.1, s)) z.2

set_option backward.isDefEq.respectTransparency false in
theorem curveVelocity_timeSlice (f : E × ℝ → M) (z : E × ℝ)
    (hf : MDifferentiableAt (𝓘(ℝ, E × ℝ)) (𝓡 n) f z) :
    curveVelocity (n := n) (fun s ↦ f (z.1, s)) z.2 =
      (mfderiv (𝓘(ℝ, E × ℝ)) (𝓡 n) f z) (0, 1) := by
  let i : ℝ → E × ℝ := fun s ↦ (z.1, s)
  have hi : HasFDerivAt i
      ((0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  change (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (f ∘ i) z.2) 1 = _
  rw [mfderiv_comp z.2 (show MDifferentiableAt (𝓘(ℝ, E × ℝ)) (𝓡 n) f (i z.2) from hf)
    hi.hasMFDerivAt.mdifferentiableAt, hi.hasMFDerivAt.mfderiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem familyPhase_contMDiffOn (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U) :
    ContMDiffOn (𝓘(ℝ, E × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞ (familyPhase (n := n) f) U := by
  have hmodel : ContMDiff ((𝓘(ℝ, E × ℝ)).prod (𝓘(ℝ, E × ℝ)))
      ((𝓘(ℝ, E × ℝ)).prod (𝓘(ℝ, E × ℝ))) ∞
      (fun z : (E × ℝ) × (E × ℝ) ↦
        (⟨z.1, z.2⟩ : TangentBundle (𝓘(ℝ, E × ℝ)) (E × ℝ))) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(ℝ, E × ℝ)) (n := ∞)) using 1
    rw [chartedSpaceSelf_prod]
    rfl
  have hs : ContMDiff (𝓘(ℝ, E × ℝ))
      ((𝓘(ℝ, E × ℝ)).prod (𝓘(ℝ, E × ℝ))) ∞
      (fun z : E × ℝ ↦ (⟨z, (0, 1)⟩ : TangentBundle (𝓘(ℝ, E × ℝ)) (E × ℝ))) :=
    hmodel.comp (contMDiff_id.prodMk contMDiff_const)
  have h := (hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn).comp
    hs.contMDiffOn (fun z hz ↦ hz)
  apply h.congr
  intro z hz
  change (⟨f z, curveVelocity (n := n) (fun s ↦ f (z.1, s)) z.2⟩ : TangentBundle (𝓡 n) M) =
    ⟨f z, (mfderivWithin (𝓘(ℝ, E × ℝ)) (𝓡 n) f U z) (0, 1)⟩
  rw [mfderivWithin_of_isOpen hU hz,
    curveVelocity_timeSlice f z ((hf.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp))]

end PoincareConjecture.Proofs.M09
