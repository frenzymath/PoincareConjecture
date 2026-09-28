import PoincareConjecture.Proofs.M08.SmoothSectionExtension
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe uV vV

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type uV} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_mfderiv_const_apply {E : Type vV}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U)
    (α : E → M) (hα : ContMDiffOn (𝓘(ℝ, E)) (𝓡 n) ∞ α U) (v : E) :
    ContMDiffOn (𝓘(ℝ, E)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (mfderiv (𝓘(ℝ, E)) (𝓡 n) α s v)) U := by
  have hv : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun s : E ↦ (⟨s, v⟩ : TangentBundle (𝓘(ℝ, E)) E)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  have htan := hα.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hcomp := htan.comp hv.contMDiffOn (fun s hs ↦ hs)
  apply hcomp.congr
  intro s hs
  change Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
      (mfderiv (𝓘(ℝ, E)) (𝓡 n) α s v) =
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
      (mfderivWithin (𝓘(ℝ, E)) (𝓡 n) α U s v)
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hs)]

theorem exists_parametricVelocityExtension {I U : Set ℝ} (hU : IsOpen U)
    (hsub : I ⊆ U) (hI : UniqueDiffOn ℝ I) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) :
    Nonempty (ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I)) := by
  have hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (curveVelocity (n := n) α s)) U :=
    contMDiffOn_mfderiv_const_apply hU α hα 1
  obtain ⟨E⟩ := exists_parametricSectionExtension hU α hα (curveVelocity (n := n) α) hY
  refine ⟨{
    extension := E.extension
    domain := E.domain
    open_domain := E.open_domain
    graph_mem := fun s hs ↦ E.graph_mem s (hsub hs)
    smooth := E.smooth
    agrees := ?_ }⟩
  intro s hs
  rw [E.agrees s (hsub hs)]
  unfold curveVelocityWithin curveVelocity
  rw [mfderivWithin_eq_mfderiv (hI.uniqueMDiffOn s hs)
    (((hα s (hsub hs)).contMDiffAt (hU.mem_nhds (hsub hs))).mdifferentiableAt (by simp))]

theorem contMDiffOn_partialTangent {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (H : ℝ × ℝ → M)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ H W)
    (v : ℝ × ℝ) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (H z)
        (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H z v)) W := by
  have hH' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H W := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hH
  have h := contMDiffOn_mfderiv_const_apply hW H hH' v
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
  exact h

theorem curveVelocity_fst_eq_partialTangent (H : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hH : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H z) :
    curveVelocity (n := n) (fun r ↦ H (r, z.2)) z.1 =
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H z (1, 0) := by
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ))
    (I' := (𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (I'' := 𝓡 n)
    (f := fun r : ℝ ↦ (r, z.2)) (g := H) z.1 hH
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const) (1 : ℝ)
  rw [mfderiv_prod_left] at hchain
  exact hchain

theorem curveVelocity_snd_eq_partialTangent (H : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hH : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H z) :
    curveVelocity (n := n) (fun r ↦ H (z.1, r)) z.2 =
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H z (0, 1) := by
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ))
    (I' := (𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (I'' := 𝓡 n)
    (f := fun r : ℝ ↦ (z.1, r)) (g := H) z.2 hH
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (1 : ℝ)
  rw [mfderiv_prod_right] at hchain
  exact hchain

theorem contMDiffOn_curveVelocity_fst {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (H : ℝ × ℝ → M)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ H W) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (H z)
        (curveVelocity (n := n) (fun r ↦ H (r, z.2)) z.1)) W := by
  apply (contMDiffOn_partialTangent hW H hH (1, 0)).congr
  intro z hz
  exact congrArg (fun w : TangentSpace (𝓡 n) (H z) ↦
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (H z) w)
      (curveVelocity_fst_eq_partialTangent H
        (((hH z hz).contMDiffAt (hW.mem_nhds hz)).mdifferentiableAt (by simp)))

theorem contMDiffOn_curveVelocity_snd {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (H : ℝ × ℝ → M)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ H W) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (H z)
        (curveVelocity (n := n) (fun r ↦ H (z.1, r)) z.2)) W := by
  apply (contMDiffOn_partialTangent hW H hH (0, 1)).congr
  intro z hz
  exact congrArg (fun w : TangentSpace (𝓡 n) (H z) ↦
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (H z) w)
      (curveVelocity_snd_eq_partialTangent H
        (((hH z hz).contMDiffAt (hW.mem_nhds hz)).mdifferentiableAt (by simp)))

theorem squareVariationField_contMDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (V.baseSquareCurve s)
        (squareVariationField V s)) ((fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain) := by
  exact (contMDiffOn_curveVelocity_snd V.square_open
    (fun z ↦ V.squareFamily z.1 z.2) V.square_smooth).comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)

theorem exists_variationDerivativeData {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) : Nonempty (LVariationDerivativeData V) := by
  classical
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  have hU : IsOpen U := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hsub : sqrtParameterInterval τ₁ τ₂ ⊆ U := by
    intro s hs
    exact V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
  have hC : UniqueDiffOn ℝ (sqrtParameterInterval τ₁ τ₂) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  obtain ⟨Evelocity⟩ := exists_parametricVelocityExtension hU hsub hC V.baseSquareCurve hα
  obtain ⟨Evariation⟩ := exists_parametricSectionExtension hU V.baseSquareCurve hα
    (squareVariationField V) (squareVariationField_contMDiffOn V)
  have hendpoint (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
      Nonempty (ParametricAlongCurveExtensionOn V.parameterDomain (V.squareFamily s)
        (curveVelocityWithin (n := n) (V.squareFamily s) V.parameterDomain)) := by
    apply exists_parametricVelocityExtension isOpen_Ioo Subset.rfl isOpen_Ioo.uniqueDiffOn
      (V.squareFamily s)
    exact V.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun t ht ↦ V.square_contains ⟨hs, ht⟩)
  exact ⟨{
    velocity_extension := Evelocity
    variation_extension := restrictParametricSectionExtension hsub Evariation
    endpoint_extension := fun s hs ↦ Classical.choice (hendpoint s hs) }⟩

end PoincareConjecture.M08
