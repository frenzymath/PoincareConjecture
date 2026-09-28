import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalInwardOrientation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnRegionTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicRegionPositiveCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Matrix Bundle
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_transverse_geodesic_return_curvature_ge_pi
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    {q : ℝ → AnnulusCoordinates} (hq : ContDiff ℝ ∞ q) {L : ℝ} (hL : 0 < L)
    (hend : q 0 = q L) (hinj : InjOn q (Ico 0 L))
    (hgeo : g.IsGeodesicOn q (Icc 0 L))
    (hunit : ∀ x ∈ Icc 0 L, g.inner (q x) (deriv q x) (deriv q x) = 1)
    (hind : LinearIndependent ℝ
      (![deriv q 0, -deriv q L] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = q '' Icc 0 L)
    (hfV : frontier V = q '' Icc 0 L)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hcompact : IsCompact (closure U)) :
    Real.pi ≤ ∫ x in closure U, D.scalarCurvature x / 2 ∂g.volumeMeasure := by
  have hregular (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) L) : deriv q x ≠ 0 := by
    intro hz
    have hu := hunit x (Ioo_subset_Icc_self hx)
    simp only [hz, map_zero] at hu
    norm_num at hu
  obtain ⟨gamma, horient, hgamma, hgammaEnd, hgammaInj, hgammaImage,
      hgammaRegular, hgammaRay⟩ :=
    m64Intrinsic_exists_global_inward_orientation hq hL hend hinj hregular
      hU hV hdisj hfU hfV
  have hgammaGeo : g.IsGeodesicOn gamma (Icc 0 L) := by
    rcases horient with rfl | rfl
    · exact hgeo
    · have h : g.IsGeodesicOn (fun x => q (-1 * x + L)) (Icc 0 L) := by
        intro x hx
        apply hgeo.comp_affine (-1) L
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have heq : (fun x => q (L - x)) = (fun x => q (-1 * x + L)) := by
        funext x
        congr 1
        ring
      rw [heq]
      exact h
  have hgammaUnit (x : ℝ) (hx : x ∈ Icc 0 L) :
      g.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1 := by
    rcases horient with rfl | rfl
    · exact hunit x hx
    · rw [deriv_comp_const_sub]
      simp only [map_neg, neg_apply, neg_neg]
      exact hunit _ ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hgammaInd : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma L] : Fin 2 → AnnulusCoordinates) := by
    rcases horient with rfl | rfl
    · exact hind
    · simp only [deriv_comp_const_sub, sub_zero, sub_self, neg_neg]
      convert hind.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.swap _ _).injective using 1
      ext i
      fin_cases i <;> simp
  have hgammaFU : frontier U = gamma '' Icc 0 L := hfU.trans hgammaImage.symm
  have hgammaFV : frontier V = gamma '' Icc 0 L := hfV.trans hgammaImage.symm
  obtain ⟨m, face, F, b, hF, hFi, hsource, hcarrier, hboundary,
      hfront, hinter, hcover⟩ :=
    m64Intrinsic_exists_return_region_triangulation hgamma hL hgammaEnd hgammaInj
      hgammaRegular hgammaInd hU hV hdisj hgammaFU hgammaFV hcompact hgammaRay
  exact m64Intrinsic_geodesic_return_region_curvature_ge_pi
    face F b hF hFi hsource hcarrier hboundary hinter hfront D hgamma hL
      hgammaEnd hgammaInj hgammaGeo hgammaUnit hU hV hdisj hgammaFU hgammaFV
      hclosure hVconn hcover

end PoincareConjecture
