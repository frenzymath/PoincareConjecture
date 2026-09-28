import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StripJetConvergence
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.CurveJetStability
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ClosedStripDifferential













set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)



theorem strip_coordinates_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (fun p : ℝ × ℝ => annulusPoint p.1 p.2) := by
  apply contMDiff_iff_contDiff.mpr
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [annulusPoint] using (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
  · simpa [annulusPoint] using (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))

omit [IsManifold (𝓡 n) ∞ M] in


theorem annulus_slice_contMDiff {f : LoopPlane → M} {V : Set ℝ} {k : ℕ∞ω}
    (hk : k ≤ ∞) (hf : ContMDiffOn (𝓡 2) (𝓡 n) k f {p | p 1 ∈ V})
    {s : ℝ} (hs : s ∈ V) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) k (fun x => f (annulusPoint x s)) := by
  have hline : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun x : ℝ => annulusPoint x s) :=
    (strip_coordinates_contMDiff.contDiff.comp
      (contDiff_id.prodMk contDiff_const)).contMDiff
  exact hf.comp_contMDiff (hline.of_le hk) (fun _ => hs)





theorem exists_annulus_slice_subarc_tolerance_of_retraction
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {time : ℝ} (htime : time ∈ Icc a b)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 2 f S)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1,
      Function.Periodic (fun x => f (annulusPoint x s)) curvePeriod)
    {s0 : ℝ} (hs0 : s0 ∈ Icc (0 : ℝ) 1)
    (himm : ∀ x, curveVelocity (n := n) (fun y => f (annulusPoint y s0)) x ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc (0 : ℝ) 1, |s - s0| < delta →
      (∀ x, curveVelocity (n := n) (fun y => f (annulusPoint y s)) x ≠ 0) ∧
      ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
        |m63ArcLength F (fun y _ => f (annulusPoint y s)) time alpha beta -
          m63ArcLength F (fun y _ => f (annulusPoint y s0)) time alpha beta| < epsilon ∧
        |m63ArcTotalCurvature F (fun y _ => f (annulusPoint y s)) time alpha beta -
          m63ArcTotalCurvature F (fun y _ => f (annulusPoint y s0)) time alpha beta| < epsilon := by
  have hc0 := annulus_slice_contMDiff (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    hf hs0
  obtain ⟨eta, heta, hgeom⟩ := exists_immersed_curve_subarc_tolerance F he hU heU hrho hre
    htime hc0 (hp s0 hs0) himm hepsilon
  let observed : ℝ × ℝ → W := fun p => e (f (annulusPoint p.1 p.2))
  have hobs : ContDiffOn ℝ 2 observed (univ ×ˢ Icc (0 : ℝ) 1) := by
    have htarget :=
      (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiffOn hf
    have hcoords := strip_coordinates_contMDiff.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact (htarget.comp hcoords.contMDiffOn (fun p hp => hp.2)).contDiffOn
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨delta, hdelta, hnear⟩ := exists_closedStrip_jet_tolerance hobs hperiod
    (fun s hs => (hp s hs).comp e) hs0 heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hdist
  exact hgeom (fun y => f (annulusPoint y s))
    (annulus_slice_contMDiff (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) hf hs)
    (hnear s hs hdist)

end PoincareConjecture.M64.RampTransport
