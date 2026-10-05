import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.PotentialNoncritical

/-!
# Smooth global annular covering coordinates

The actual noncritical gradient makes the literal normalized Jacobian
positive. The global homeomorphism consequently has a smooth inverse
at every point, by the inverse function theorem. Its actual open source
and target and full normalized coordinate formula are retained.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- Nonzero retained gradient gives a strictly positive literal normalized Jacobian, using
the actual polar density identity. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarNormalizedCoverMap_det_pos {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P) {z : Cover} (hz : z ∈ scalarCoverStrip)
    (hgrad : D.gradient H (scalarCoverMap z) ≠ 0) :
    0 < (fderiv ℝ (scalarNormalizedCoverMap H V P) z).det := by
  rw [scalarNormalizedCoverMap_det D hHs hdV P hz,
    scalarCoverJacobian_eq_metric_energy D hHs hz]
  have hrho : 0 < g.pullbackVolumeDensity id (scalarCoverMap z) :=
    (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
      (by simpa using Function.injective_id)).2
  exact div_pos (mul_pos (mul_pos
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (zero_lt_one.trans hz.1)) hrho)
      (g.pos _ _ hgrad)) hP

/-- The actual normalized differential is an equivalence at every point with nonzero
retained gradient. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit
project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarNormalizedCoverMap_fderiv_invertible {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P) {z : Cover} (hz : z ∈ scalarCoverStrip)
    (hgrad : D.gradient H (scalarCoverMap z) ≠ 0) :
    (fderiv ℝ (scalarNormalizedCoverMap H V P) z).IsInvertible := by
  let A := fderiv ℝ (scalarNormalizedCoverMap H V P) z
  have hdet : A.toLinearMap.det ≠ 0 :=
    (scalarNormalizedCoverMap_det_pos D hHs hdV hP hz hgrad).ne'
  have hker : LinearMap.ker A.toLinearMap = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  exact ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

/-- The actual smooth potential and conjugate give smooth normalized coordinates throughout
their open covering strip. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarNormalizedCoverMap_smooth {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hVs : ContDiffOn ℝ ∞ V scalarCoverStrip) (P : ℝ) :
    ContDiffOn ℝ ∞ (scalarNormalizedCoverMap H V P) scalarCoverStrip := by
  have hVn : ContDiffOn ℝ ∞ (fun z => V z / P) scalarCoverStrip := by
    have hconst : ContDiffOn ℝ ∞ (fun _ : Cover => P⁻¹) scalarCoverStrip := contDiffOn_const
    convert! (hconst.mul hVs) using 1
    ext z
    exact div_eq_inv_mul (V z) P
  exact (scalarCoverPotential_smooth hHs).prodMk hVn

/-- Every smooth annular metric supplies an actual global smooth chart from the polar cover
to the normalized potential strip. Both directions are smooth, and the chart is the
constructed harmonic-conjugate map. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem exists_smooth_annular_cover_chart :
    ∃ (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ)
      (e : OpenPartialHomeomorph Cover Cover),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      0 < P ∧ P = scalarFluxPeriod D H (3 / 2) ∧
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      e.source = scalarCoverStrip ∧ e.target = scalarPotentialStrip ∧
      (e : Cover → Cover) = scalarNormalizedCoverMap H V P ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1) := by
  obtain ⟨H, V, P, hHc, hHs, hlap, hinner, houter, hgrad, hP, hPeq,
    hVs, hdV, hdeck, hrange, hhomeo⟩ := exists_noncritical_homeomorphic_annular_cover_conjugate D
  let F := scalarNormalizedCoverMap H V P
  have hinj : InjOn F scalarCoverStrip := by
    intro x hx y hy hxy
    have h := hhomeo.injective (show scalarNormalizedCover H V P hrange ⟨x, hx⟩ =
        scalarNormalizedCover H V P hrange ⟨y, hy⟩ from Subtype.ext hxy)
    exact congrArg Subtype.val h
  have hopen : IsOpenMap (scalarCoverStrip.domRestrict F) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    have h := scalarNormalizedCoverMap_nhds_le_map D hHc hHs hlap hinner houter hdV hP.ne'
      z.property
    rw [← scalarCoverStrip_isOpen.nhdsWithin_eq z.property, ← map_nhds_subtype_val,
      map_map] at h
    exact h
  have hFs : ContDiffOn ℝ ∞ F scalarCoverStrip := scalarNormalizedCoverMap_smooth hHs hVs P
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv F scalarCoverStrip) hFs.continuousOn hopen scalarCoverStrip_isOpen
  have htarget : e.target = scalarPotentialStrip := by
    change F '' scalarCoverStrip = scalarPotentialStrip
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hrange _ (scalarCoverMap_mem hz)
    · intro z hz
      obtain ⟨x, hx⟩ := hhomeo.surjective ⟨z, hz⟩
      exact ⟨x, x.property, congrArg Subtype.val hx⟩
  have hEs : ContDiffOn ℝ ∞ e e.source := hFs
  have hEi : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hx : e.symm y ∈ scalarCoverStrip := e.map_target hy
    have hs := hEs.contDiffAt (e.open_source.mem_nhds hx)
    obtain ⟨L, hL⟩ := scalarNormalizedCoverMap_fderiv_invertible D hHs hdV hP hx
      (hgrad _ (scalarCoverMap_mem hx))
    have hD : HasFDerivAt e (L : Cover →L[ℝ] Cover) (e.symm y) := by
      rw [hL]
      exact (hs.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hD hs).contDiffWithinAt
  exact ⟨H, V, P, e, hHc, hHs, hlap, hinner, houter, hP, hPeq, hVs, hdV, rfl, htarget,
    rfl, hEs, hEi, fun z hz => scalarNormalizedCoverMap_deck (H := H) hP.ne' hdeck hz⟩

end PoincareMT.M64Uniformization
