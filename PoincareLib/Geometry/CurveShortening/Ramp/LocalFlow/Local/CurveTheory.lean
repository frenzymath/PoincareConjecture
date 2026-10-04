import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlowTheory
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Intrinsic.C2LocalExistence
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Smooth.LocalExistence
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Uniqueness.Fields
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Arbitrary.C2IntrinsicRegularity
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Smooth.InitialUpgrade
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.C2.Continuation
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Continuous.Dependence
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Fixed.RelabelingAssembly

/-!
# Actual local curve theory on a compact ambient manifold

The spectral constructions, fixed-label uniqueness, intrinsic regularity
and compact-family limit supply all nine frozen local-theory fields.
MT2007 Claim 19.1, p. 437, and Lemmas 19.14/19.17, pp. 446-450;
`2026-09-23-local-curve-theory-assembly.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- Actual compact local curve theory, including C2 existence and trace,
uniqueness, continuation, smooth upgrade and compact-family dependence.
MT2007 Claim 19.1, p. 437; local curve theory assembly derivation. -/
theorem localCurveTheory_of_compact
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M)) :
    M63LocalCurveTheory F := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  exact
    { local_existence := by
        intro gamma hperiod hC2 himm
        obtain ⟨T, haT, hTb, c, hc, hc0, hi⟩ :=
          exists_intrinsic_c2_local_curve F gamma hperiod hC2 himm
        exact ⟨T, haT, hTb.le, c, hc, hc0, hi⟩
      smooth_local_existence := by
        intro gamma hperiod hsmooth himm
        obtain ⟨T, haT, hTb, c, hc, hc0, hi, _hjoint⟩ :=
          exists_smooth_local_curve F gamma hperiod hsmooth himm
        exact ⟨T, haT, hTb.le, c, hc, hc0, hi⟩
      unique_closed := fun _T _haT _hTb _c _d hc hd hinit =>
        c2ShrinkingCurve_unique_closed F hcompact hc hd hinit
      unique_half_open := fun _T haT hTb _c _d hc hd hinit =>
        c2ShrinkingCurve_unique_half_open F hcompact haT hTb hc hd hinit
      intrinsic_regularity := fun _T haT hTb _J hJ _c hc =>
        c2ShrinkingCurve_intrinsic_regularity F hcompact haT hTb hJ hc
      smooth_initial_upgrade := fun _T haT hTb _J hJ _c hc hinitial =>
        c2ShrinkingCurve_smooth_of_smooth_initial F hcompact haT hTb hJ hc
          (c2ShrinkingCurve_intrinsic_regularity F hcompact haT hTb hJ hc) hinitial
      continuation := fun _T haT hTb _c hc _K hK hcurv =>
        c2ShrinkingCurve_continuation F hcompact haT hTb hc hK hcurv
      continuous_dependence := by
        intro Z _ _ gamma hgamma hfirst hsecond hperiod hC2 himm
        exact exists_compact_c2_curve_family F hab hcompact Z gamma
          hgamma hfirst hsecond hperiod hC2 himm
      fixed_relabeling := fun _T haT hTb _J hJ _c hc _tau _s hat hts _hsT hslab =>
        exists_fixed_smooth_relabeling F hcompact hc
          (c2ShrinkingCurve_intrinsic_regularity F hcompact haT hTb hJ hc)
          hat hts hslab }

end PoincareMT.M63
