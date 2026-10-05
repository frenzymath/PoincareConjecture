import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Periodic.JetTolerance
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Actual horizontal slice jets on a closed C2 strip

Within derivatives on the full closed strip identify the first and
second ordinary derivatives of each horizontal slice, including both
radial endpoints. Source: MT2007 Lemma 19.31, pp. 464-466; ramp transport
trimming derivation, horizontal jets at radial endpoints.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology ContDiff

namespace PoincareMT.M64.RampTransport

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

local notation "S" => Set.prod (univ : Set ℝ) (Icc (0 : ℝ) 1)

/-- The literal observed three-jet of a horizontal slice. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
noncomputable def horizontalSliceJet (f : ℝ × ℝ → W) (p : ℝ × ℝ) : W × W × W :=
  (f p, deriv (fun x => f (x, p.2)) p.1,
    deriv (deriv (fun x => f (x, p.2))) p.1)

/-- Every horizontal slice retains the regularity of the closed strip.
Source: MT Lemma 19.31, pp. 464-466; horizontal-jet trimming derivation. -/
theorem closedStrip_slice_contDiff {f : ℝ × ℝ → W} {k : ℕ∞ω}
    (hf : ContDiffOn ℝ k f S) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ k (fun x => f (x, s)) :=
  hf.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hs⟩)

/-- These are the actual slice derivatives, obtained from within derivatives without
extending the map across a radial boundary. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem closedStrip_horizontal_derivatives {f : ℝ × ℝ → W}
    (hf : ContDiffOn ℝ 2 f S) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    deriv (fun y => f (y, s)) x = fderivWithin ℝ f S (x, s) (1, 0) ∧
      deriv (deriv (fun y => f (y, s))) x =
        fderivWithin ℝ (fun p => fderivWithin ℝ f S p (1, 0)) S (x, s) (1, 0) := by
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod uniqueDiffOn_Icc_zero_one
  have hV : ContDiffOn ℝ 1 (fun p => fderivWithin ℝ f S p (1, 0)) S :=
    (hf.fderivWithin hS (by norm_num)).clm_apply contDiffOn_const
  have hline (y : ℝ) : HasDerivAt (fun z : ℝ => (z, s)) (1, 0) y :=
    (hasDerivAt_id y).prodMk (hasDerivAt_const y s)
  have hfirst (y : ℝ) : deriv (fun z => f (z, s)) y =
      fderivWithin ℝ f S (y, s) (1, 0) := by
    have hd := (hf.differentiableOn (by norm_num) (y, s) ⟨mem_univ _, hs⟩).hasFDerivWithinAt
    exact (hd.comp_hasDerivAt y (hline y)
      (show ∀ᶠ z : ℝ in 𝓝 y, (z, s) ∈ S from
        Eventually.of_forall (fun _ => ⟨mem_univ _, hs⟩))).deriv
  refine ⟨hfirst x, ?_⟩
  rw [show deriv (fun y => f (y, s)) =
    (fun y => fderivWithin ℝ f S (y, s) (1, 0)) from funext hfirst]
  have hd := (hV.differentiableOn (by norm_num) (x, s) ⟨mem_univ _, hs⟩).hasFDerivWithinAt
  exact (hd.comp_hasDerivAt x (hline x)
    (show ∀ᶠ z : ℝ in 𝓝 x, (z, s) ∈ S from
      Eventually.of_forall (fun _ => ⟨mem_univ _, hs⟩))).deriv

/-- Actual horizontal three-jets vary continuously on the closed strip. Source: Morgan--Tian
Lemma 19.31, printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem horizontalSliceJet_continuousOn {f : ℝ × ℝ → W}
    (hf : ContDiffOn ℝ 2 f S) : ContinuousOn (horizontalSliceJet f) S := by
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod uniqueDiffOn_Icc_zero_one
  have hV : ContDiffOn ℝ 1 (fun p => fderivWithin ℝ f S p (1, 0)) S :=
    (hf.fderivWithin hS (by norm_num)).clm_apply contDiffOn_const
  have hW := (hV.continuousOn_fderivWithin hS (by norm_num)).clm_apply
    (continuousOn_const (c := ((1 : ℝ), (0 : ℝ))))
  apply (hf.continuousOn.prodMk (hV.continuousOn.prodMk hW)).congr
  intro p hp
  rcases p with ⟨x, s⟩
  obtain ⟨h1, h2⟩ := closedStrip_horizontal_derivatives hf hp.2 x
  exact Prod.ext rfl (Prod.ext h1 h2)

end PoincareMT.M64.RampTransport
