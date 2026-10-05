import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.CoverOpen

/-!
# Actual surjectivity of the normalized annular conjugate map

The constructed map is proper and open. Its nonempty image is therefore
both closed and open in the connected potential strip. This proves
surjectivity before critical-point exclusion or injectivity, and does
not silently assume that the map is an unbranched covering.

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

/-- The actual positive-period normalized conjugate map fills the entire potential strip.
Branch exclusion is not used in this argument. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-conjugate-open-surjective.md`. -/
theorem scalarNormalizedCover_surjective {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hVc : ContinuousOn V scalarCoverStrip)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective (scalarNormalizedCover H V P hrange) := by
  have hconvex : Convex ℝ scalarPotentialStrip :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  let : PreconnectedSpace scalarPotentialStrip :=
    Subtype.preconnectedSpace hconvex.isPreconnected
  have hopen := scalarNormalizedCover_isOpenMap D hHc hHs hlap hinner houter hdV hP.ne' hrange
  have hproper := scalarNormalizedCover_isProperMap hHc hinner houter hrange hVc hP hdeck
  have hclopen : IsClopen (range (scalarNormalizedCover H V P hrange)) :=
    ⟨hproper.isClosedMap.isClosed_range, hopen.isOpen_range⟩
  have hfull : range (scalarNormalizedCover H V P hrange) = univ := by
    apply (isClopen_iff.mp hclopen).resolve_left
    intro hempty
    let z : scalarCoverStrip := ⟨(3 / 2, 0), by norm_num [scalarCoverStrip]⟩
    have hmem := mem_range_self (f := scalarNormalizedCover H V P hrange) z
    rw [hempty] at hmem
    exact hmem
  exact range_eq_univ.mp hfull

/-- Every actual smooth annular metric supplies an actual positive-period conjugate whose
normalized map is proper, open, and surjective. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-conjugate-open-surjective.md`. -/
theorem exists_proper_open_surjective_annular_cover_conjugate :
    ∃ (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      0 < P ∧ P = scalarFluxPeriod D H (3 / 2) ∧
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      (∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) ∧
      ∃ hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1,
        IsProperMap (scalarNormalizedCover H V P hrange) ∧
        IsOpenMap (scalarNormalizedCover H V P hrange) ∧
        Function.Surjective (scalarNormalizedCover H V P hrange) := by
  obtain ⟨H, V, P, hHc, hHs, hlap, hinner, houter, hP, hPeq, hVs, hdV, hdeck,
    hrange, hproper⟩ := exists_proper_annular_cover_conjugate D
  exact ⟨H, V, P, hHc, hHs, hlap, hinner, houter, hP, hPeq, hVs, hdV, hdeck,
    hrange, hproper,
    scalarNormalizedCover_isOpenMap D hHc hHs hlap hinner houter hdV hP.ne' hrange,
    scalarNormalizedCover_surjective D hHc hHs hlap hinner houter hVs.continuousOn
      hdV hP hdeck hrange⟩

end PoincareMT.M64Uniformization
