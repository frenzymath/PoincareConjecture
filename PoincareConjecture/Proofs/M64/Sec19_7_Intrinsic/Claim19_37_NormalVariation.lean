import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_BoundaryNormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.GeodesicFlow
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.InitialData

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_isGeodesicOn_of_phase
    (N : IntrinsicAnnulus) {phase : ℝ → AnnulusCoordinates × AnnulusCoordinates}
    {J : Set ℝ} (hJ : IsOpen J)
    (hphase : ∀ t ∈ J, HasDerivAt phase
      (coordinateGeodesicField N.metric.euclideanCoefficients (phase t)) t) :
    N.metric.IsGeodesicOn (fun t => (phase t).1) J := by
  have hcoeff : N.metric.pullbackCoefficients (extChartAt (𝓡 2) (0 : AnnulusCoordinates)).symm =
      N.metric.euclideanCoefficients := by
    ext p v w
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe]
    change N.metric.inner p (mfderiv (𝓡 2) (𝓡 2) id p v)
      (mfderiv (𝓡 2) (𝓡 2) id p w) = N.metric.inner p v w
    rw [mfderiv_id]
    rfl
  have h := N.metric.isGeodesicOn_chart_curve (0 : AnnulusCoordinates) hJ
    (q := fun t => (phase t).1) (w := fun t => (phase t).2) (by
      intro t ht
      refine ⟨by simp, ?_, ?_⟩
      · simpa [coordinateGeodesicField] using (hphase t ht).hasFDerivAt.fst.hasDerivAt
      · rw [hcoeff]
        simpa [coordinateGeodesicField] using (hphase t ht).hasFDerivAt.snd.hasDerivAt)
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq] using! h

theorem m64Intrinsic_exists_local_geodesic_variation
    (N : IntrinsicAnnulus) {gamma velocity : ℝ → AnnulusCoordinates}
    (hgamma : ContDiff ℝ ∞ gamma) (hvelocity : ContDiff ℝ ∞ velocity) (a : ℝ) :
    ∃ (U : Set ℝ) (delta : ℝ)
      (phase : ℝ × ℝ → AnnulusCoordinates × AnnulusCoordinates),
      IsOpen U ∧ a ∈ U ∧ 0 < delta ∧
      ContDiffOn ℝ ∞ phase (U ×ˢ Ioo (-delta) delta) ∧
      (∀ x ∈ U, phase (x, 0) = (gamma x, velocity x)) ∧
      (∀ x ∈ U, ∀ t ∈ Ioo (-delta) delta,
        HasDerivAt (fun s => phase (x, s))
          (coordinateGeodesicField N.metric.euclideanCoefficients (phase (x, t))) t) ∧
      (∀ x ∈ U, N.metric.IsGeodesicOn (fun t => (phase (x, t)).1)
        (Ioo (-delta) delta)) ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-delta) delta,
        N.metric.inner (phase (x, t)).1 (phase (x, t)).2 (phase (x, t)).2 =
          N.metric.inner (gamma x) (velocity x) (velocity x) := by
  have hB : ContDiffOn ℝ ∞ N.metric.euclideanCoefficients univ :=
    (contDiff_iff_contDiffAt.mpr N.metric.contDiffAt_euclideanCoefficients).contDiffOn
  obtain ⟨V, delta, Phi, hV, ha, _, hdelta, hPhi, hinit, hflow⟩ :=
    exists_smooth_coordinate_geodesic_flow isOpen_univ hB
      (fun x _ => N.metric.inner_isInvertible x)
      (fun x _ v w => N.metric.symm x v w) (mem_univ (gamma a)) (velocity a)
  let initial : ℝ → AnnulusCoordinates × AnnulusCoordinates := fun x => (gamma x, velocity x)
  let U := initial ⁻¹' V
  let phase : ℝ × ℝ → AnnulusCoordinates × AnnulusCoordinates :=
    fun z => Phi (initial z.1, z.2)
  have hinitial : ContDiff ℝ ∞ initial := hgamma.prodMk hvelocity
  have hU : IsOpen U := hV.preimage hinitial.continuous
  have hsmooth : ContDiffOn ℝ ∞ phase (U ×ˢ Ioo (-delta) delta) := by
    exact hPhi.comp
      ((hinitial.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hz.1, hz.2⟩)
  have hphase (x : ℝ) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo (-delta) delta) :
      HasDerivAt (fun s => phase (x, s))
        (coordinateGeodesicField N.metric.euclideanCoefficients (phase (x, t))) t :=
    (hflow (initial x) hx t ht).2.1
  refine ⟨U, delta, phase, hU, ha, hdelta, hsmooth, ?_, hphase, ?_, ?_⟩
  · intro x hx
    exact hinit (initial x) hx
  · intro x hx
    exact m64Intrinsic_isGeodesicOn_of_phase N isOpen_Ioo (hphase x hx)
  · intro x hx t ht
    exact (hflow (initial x) hx t ht).2.2

theorem m64Intrinsic_exists_local_normal_geodesic_variation
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) :
    ∃ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal ∧
      (∀ t, N.metric.inner (intrinsicAnnulusBoundary radius t) (normal t) (normal t) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary radius t) (normal t)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) t) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary radius t) (normal t)) ∧
      ∀ a : ℝ, ∃ (U : Set ℝ) (delta : ℝ)
        (phase : ℝ × ℝ → AnnulusCoordinates × AnnulusCoordinates),
        IsOpen U ∧ a ∈ U ∧ 0 < delta ∧
        ContDiffOn ℝ ∞ phase (U ×ˢ Ioo (-delta) delta) ∧
        (∀ x ∈ U, phase (x, 0) = (intrinsicAnnulusBoundary radius x, normal x)) ∧
        (∀ x ∈ U, N.metric.IsGeodesicOn (fun t => (phase (x, t)).1)
          (Ioo (-delta) delta)) ∧
        ∀ x ∈ U, ∀ t ∈ Ioo (-delta) delta,
          HasDerivAt (fun s => (phase (x, s)).1) (phase (x, t)).2 t ∧
          N.metric.inner (phase (x, t)).1 (phase (x, t)).2 (phase (x, t)).2 = 1 := by
  obtain ⟨normal, hnormal, hn⟩ := m64Intrinsic_exists_smooth_inward_boundary_normal N hradius
  refine ⟨normal, hnormal, hn, ?_⟩
  intro a
  obtain ⟨U, delta, phase, hU, ha, hdelta, hsmooth, hinit, hphase, hgeo, henergy⟩ :=
    m64Intrinsic_exists_local_geodesic_variation N (m64Intrinsic_contDiff_boundary radius) hnormal a
  refine ⟨U, delta, phase, hU, ha, hdelta, hsmooth, hinit, hgeo, ?_⟩
  intro x hx t ht
  refine ⟨?_, (henergy x hx t ht).trans (hn x).1⟩
  simpa [coordinateGeodesicField] using (hphase x hx t ht).hasFDerivAt.fst.hasDerivAt

end PoincareConjecture
