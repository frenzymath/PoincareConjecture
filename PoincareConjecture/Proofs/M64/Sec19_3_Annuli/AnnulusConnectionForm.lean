import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapLocalFlux
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationFlatDevelopment
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationSphereCurvature












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem annulus_plane_field_smoothAt
    {X : LoopPlane → LoopPlane} {p : LoopPlane} (hX : ContDiffAt ℝ ∞ X p) :
    ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡 2) LoopPlane)) p := by
  rw [contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_iff_contDiffAt.mpr hX⟩






theorem m64Annulus_connectionForm_curvature_integral
    (g : RiemannianMetric 2 LoopPlane) (D : LeviCivitaData g)
    (e0 e1 : LoopPlane → LoopPlane) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (he0 : ContDiffOn ℝ ∞ e0 O) (he1 : ContDiffOn ℝ ∞ e1 O)
    (hunit0 : ∀ p ∈ O, g.inner p (e0 p) (e0 p) = 1)
    (hunit1 : ∀ p ∈ O, g.inner p (e1 p) (e1 p) = 1)
    (horth : ∀ p ∈ O, g.inner p (e0 p) (e1 p) = 0)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      g.inner (annulusPoint curvePeriod s)
          (D.connection e0 (annulusPoint curvePeriod s) (EuclideanSpace.single (1 : Fin 2) 1))
          (e1 (annulusPoint curvePeriod s)) =
        g.inner (annulusPoint 0 s)
          (D.connection e0 (annulusPoint 0 s) (EuclideanSpace.single (1 : Fin 2) 1))
          (e1 (annulusPoint 0 s))) :
    (∫ p in m64AnnulusDomain,
      D.curvatureTensor p (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1) (e1 p) (e0 p)) +
      (∫ x in Icc (0 : ℝ) curvePeriod,
        g.inner (annulusPoint x 1)
            (D.connection e0 (annulusPoint x 1) (EuclideanSpace.single (0 : Fin 2) 1))
            (e1 (annulusPoint x 1)) -
          g.inner (annulusPoint x 0)
            (D.connection e0 (annulusPoint x 0) (EuclideanSpace.single (0 : Fin 2) 1))
            (e1 (annulusPoint x 0))) = 0 := by
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let X : LoopPlane → LoopPlane := fun _ => b0
  let Y : LoopPlane → LoopPlane := fun _ => b1
  let w0 := D.surfaceConnectionForm e0 e1 X
  let w1 := D.surfaceConnectionForm e0 e1 Y
  have hfield0 : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun p => (⟨p, e0 p⟩ : TangentBundle (𝓡 2) LoopPlane)) O := by
    intro p hp
    exact (annulus_plane_field_smoothAt (he0.contDiffAt (hO.mem_nhds hp))).contMDiffWithinAt
  have hfield1 : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun p => (⟨p, e1 p⟩ : TangentBundle (𝓡 2) LoopPlane)) O := by
    intro p hp
    exact (annulus_plane_field_smoothAt (he1.contDiffAt (hO.mem_nhds hp))).contMDiffWithinAt
  have hX (p : LoopPlane) : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡 2) LoopPlane)) p :=
    annulus_plane_field_smoothAt contDiffAt_const
  have hY (p : LoopPlane) : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q => (⟨q, Y q⟩ : TangentBundle (𝓡 2) LoopPlane)) p :=
    annulus_plane_field_smoothAt contDiffAt_const
  have hw0 : ContDiffOn ℝ ∞ w0 O := by
    intro p hp
    exact (contMDiffAt_iff_contDiffAt.mp
      (D.contMDiffAt_inner_covariantDerivativeOnFields (hX p)
        (hfield0.contMDiffAt (hO.mem_nhds hp))
        (hfield1.contMDiffAt (hO.mem_nhds hp)))).contDiffWithinAt
  have hw1 : ContDiffOn ℝ ∞ w1 O := by
    intro p hp
    exact (contMDiffAt_iff_contDiffAt.mp
      (D.contMDiffAt_inner_covariantDerivativeOnFields (hY p)
        (hfield0.contMDiffAt (hO.mem_nhds hp))
        (hfield1.contMDiffAt (hO.mem_nhds hp)))).contDiffWithinAt
  have hbracket : mlieBracket (𝓡 2) X Y = 0 := by
    funext p
    simp only [X, Y, mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
    simp +instances
  have hcurv (p : LoopPlane) (hp : p ∈ O) :
      D.curvatureTensor p b0 b1 (e1 p) (e0 p) =
        fderiv ℝ w1 p b0 - fderiv ℝ w0 p b1 := by
    have h := D.curvatureTensor_eq_exteriorDerivative_surfaceConnectionForm hO hp
      hfield0 hfield1 hunit0 hunit1 horth (hX p) (hY p)
    rw [hbracket] at h
    simpa [w0, w1, X, Y, mvfderiv, mfderiv_eq_fderiv,
      LeviCivitaData.surfaceConnectionForm, LeviCivitaData.covariantDerivativeOnFields,
      NormedSpace.fromTangentSpace] using! h
  have hi0 : IntegrableOn (fun p => fderiv ℝ w0 p b1) m64AnnulusDomain volume :=
    (((hw0.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
      |>.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
  have hi1 : IntegrableOn (fun p => fderiv ℝ w1 p b0) m64AnnulusDomain volume :=
    (((hw1.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
      |>.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
  have heq : (∫ p in m64AnnulusDomain, D.curvatureTensor p b0 b1 (e1 p) (e0 p)) =
      (∫ p in m64AnnulusDomain, fderiv ℝ w1 p b0) -
        ∫ p in m64AnnulusDomain, fderiv ℝ w0 p b1 := by
    rw [← integral_sub hi1 hi0]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
    exact hcurv p (hdom hp)
  have hhorizontal : (∫ p in m64AnnulusDomain, fderiv ℝ w1 p b0) = 0 := by
    rw [m64Annulus_restrict_closed_eq_interior,
      m64Annulus_integral_horizontal_derivative_of_contDiffOn hO hdom hw1]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact sub_eq_zero.mpr (hseam s hs)
  have hvertical := m64Annulus_integral_vertical_derivative_of_contDiffOn hO hdom hw0
  rw [← m64Annulus_restrict_closed_eq_interior] at hvertical
  rw [hhorizontal, hvertical] at heq
  change (∫ p in m64AnnulusDomain, D.curvatureTensor p b0 b1 (e1 p) (e0 p)) +
    (∫ x in Icc (0 : ℝ) curvePeriod, w0 (annulusPoint x 1) - w0 (annulusPoint x 0)) = 0
  linarith

end PoincareConjecture
