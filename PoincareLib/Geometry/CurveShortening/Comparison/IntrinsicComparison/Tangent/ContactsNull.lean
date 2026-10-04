import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Tangent.ContactChart
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Polar.Inverse

/-!
# Null base labels of all regular tangent contacts

Actual inverse charts cover every regular point of a smooth normal map.
Second countability reduces them to a countable cover, so the local
critical-value nullity controls every tangent target contact over the
same base label. This formal tool supports the retained-base treatment
of Morgan--Tian, Lemma 19.46, pp. 474-477; see
`derivations/2026-09-25-null-tangent-contact-bases.md`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The base labels of all regular tangent contacts with a smooth target
curve form a null set. No stopping height, global injection, or target
regularity is required; only the differential at the contact is regular.
This supports the formal retained-base treatment of Morgan--Tian,
Lemma 19.46, printed pp. 474-477. -/
theorem m64Intrinsic_curve_tangent_bases_null
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target) :
    volume {a : ℝ | ∃ t s : ℝ,
      e !₂[a, t] = target s ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) ∧
      ¬ LinearIndependent ℝ
        (![deriv target s, fderiv ℝ e !₂[a, t] !₂[0, 1]] :
          Fin 2 → AnnulusCoordinates)} = 0 := by
  classical
  let I := {x : AnnulusCoordinates //
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) e x)}
  have hInv (x : I) :
      ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
        x.1 ∈ F.source ∧ (F : AnnulusCoordinates → AnnulusCoordinates) = e ∧
        ContDiffOn ℝ ∞ F.symm F.target := by
    obtain ⟨F, hx, _, hF, _, hFi⟩ :=
      m64Intrinsic_exists_smooth_polar_inverse isOpen_univ
        (contMDiff_iff_contDiff.mpr he).contMDiffOn (mem_univ x.1) x.2
    exact ⟨F, hx, hF, hFi⟩
  choose F hpoint hF hFi using hInv
  obtain ⟨C, hCcount, hCcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : I => (F x).source) (fun x => (F x).open_source)
  let bad (x : I) : Set ℝ := {a | ∃ t s : ℝ,
    !₂[a, t] ∈ (F x).source ∧ e !₂[a, t] = target s ∧
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) ∧
    ¬ LinearIndependent ℝ
      (![deriv target s, fderiv ℝ e !₂[a, t] !₂[0, 1]] :
        Fin 2 → AnnulusCoordinates)}
  have hbad (x : I) : volume (bad x) = 0 :=
    m64Intrinsic_curve_tangent_chart_bases_null e he (F x) (hF x) (hFi x) htarget
  have hnull : volume (⋃ x ∈ C, bad x) = 0 :=
    (measure_biUnion_null_iff hCcount).2 (fun x _ => hbad x)
  apply measure_mono_null ?_ hnull
  rintro a ⟨t, s, hend, hregular, htangent⟩
  let x : I := ⟨!₂[a, t], hregular⟩
  have hmem : !₂[a, t] ∈ ⋃ y : I, (F y).source :=
    mem_iUnion.mpr ⟨x, hpoint x⟩
  rw [← hCcover] at hmem
  obtain ⟨y, hy⟩ := mem_iUnion.mp hmem
  obtain ⟨hyC, hsource⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr
    ⟨hyC, t, s, hsource, hend, hregular, htangent⟩⟩

end PoincareMT
