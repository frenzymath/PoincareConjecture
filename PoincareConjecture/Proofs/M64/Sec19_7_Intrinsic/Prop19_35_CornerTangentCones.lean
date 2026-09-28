import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalTangentCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.GeneralBoundaryFans

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_inverse_coordinate_derivative_apply
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {q : AnnulusCoordinates} (hq : q ∈ F.target) (k : Fin 3) (w : AnnulusCoordinates) :
    fderiv ℝ (fun x => b.coord k (F.symm x)) q w =
      (b.coord k).linear (fderiv ℝ F.symm q w) := by
  let c : AnnulusCoordinates →ᴬ[ℝ] ℝ :=
    { toAffineMap := b.coord k, cont := (b.coord k).continuous_of_finiteDimensional }
  have hdi : DifferentiableAt ℝ F.symm q :=
    (((contMDiffOn_iff_contDiffOn.mp hFi) q hq).contDiffAt
      (F.open_target.mem_nhds hq)).differentiableAt (by simp)
  have hd : fderiv ℝ (fun x => b.coord k (F.symm x)) q =
      c.contLinear.comp (fderiv ℝ F.symm q) :=
    (c.hasFDerivAt.comp q hdi.hasFDerivAt).fderiv
  rw [hd]
  rfl

private theorem corner_linear_decomposition
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates) (v : AnnulusCoordinates) :
    v = (b.coord 1).linear v • (b 1 - b 0) +
      (b.coord 2).linear v • (b 2 - b 0) := by
  have h := affineBasis_vsub_zero_eq b (v + b 0)
  have hcoord (k : Fin 3) :
      b.coord k (v + b 0) = (b.coord k).linear v + b.coord k (b 0) := by
    simpa only [vadd_eq_add] using (b.coord k).map_vadd (b 0) v
  simpa only [add_sub_cancel_right, hcoord,
    b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
    b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0), add_zero] using h

theorem m64Intrinsic_coordinate_corner_tangent_cone
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (w : AnnulusCoordinates) :
    (∀ k, b.coord k (F.symm (F (b 0))) = 0 →
      0 < fderiv ℝ (fun x => b.coord k (F.symm x)) (F (b 0)) w) ↔
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      w = a • fderiv ℝ F (b 0) (b 1 - b 0) +
        c • fderiv ℝ F (b 0) (b 2 - b 0) := by
  have hb0 : b 0 ∈ F.source := hsource (subset_convexHull ℝ _ (mem_range_self 0))
  have hqt := F.map_source hb0
  have hD : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  let L := fderiv ℝ F (b 0)
  let J := fderiv ℝ F.symm (F (b 0))
  have hJL (v : AnnulusCoordinates) : J (L v) = v := by
    have h := hD.symm_comp_deriv hb0
    simp only [mfderiv_eq_fderiv, TangentSpace] at h
    exact congrArg (fun A : AnnulusCoordinates →L[ℝ] AnnulusCoordinates => A v) h
  have hLJ (v : AnnulusCoordinates) : L (J v) = v := by
    have h := hD.comp_symm_deriv hqt
    rw [F.left_inv hb0] at h
    simp only [mfderiv_eq_fderiv, TangentSpace] at h
    exact congrArg (fun A : AnnulusCoordinates →L[ℝ] AnnulusCoordinates => A v) h
  have hd (k : Fin 3) :
      fderiv ℝ (fun x => b.coord k (F.symm x)) (F (b 0)) w =
        (b.coord k).linear (J w) :=
    m64Intrinsic_inverse_coordinate_derivative_apply F b hFi hqt k w
  have hvalues (k i j : Fin 3) :
      (b.coord k).linear (b i - b j) = b.coord k (b i) - b.coord k (b j) :=
    (b.coord k).linearMap_vsub _ _
  constructor
  · intro hpositive
    have hpos1 := hpositive 1 (by
      rw [F.left_inv hb0, b.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0)])
    have hpos2 := hpositive 2 (by
      rw [F.left_inv hb0, b.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0)])
    rw [hd] at hpos1 hpos2
    refine ⟨(b.coord 1).linear (J w), (b.coord 2).linear (J w), hpos1, hpos2, ?_⟩
    have h := congrArg L (corner_linear_decomposition b (J w))
    rw [hLJ, map_add, map_smul, map_smul] at h
    exact h
  · rintro ⟨a, c, ha, hc, hw⟩ k hk
    have hJw : J w = a • (b 1 - b 0) + c • (b 2 - b 0) := by
      rw [hw, map_add, map_smul, map_smul, hJL, hJL]
    rw [F.left_inv hb0] at hk
    rw [hd, hJw, map_add, map_smul, map_smul, hvalues, hvalues]
    fin_cases k
    · norm_num [AffineBasis.coord_apply] at hk
    · simpa [AffineBasis.coord_apply, Fin.ext_iff] using ha
    · simpa [AffineBasis.coord_apply, Fin.ext_iff] using hc

end PoincareConjecture
