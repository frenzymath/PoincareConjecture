import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapChordSigns
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CapSeparation













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture





theorem m64Intrinsic_exists_cap_endpoint_separator
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T r : ℝ} (hr : 0 < r)
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hF : ContDiffOn ℝ ∞ F F.source) (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    (hchord : ∀ t : ℝ, F ((1 - t) * r, t * r) =
      (1 - t) • F (r, 0) + t • F (0, r))
    (terminal vertical : Bool)
    (haxis : ∀ s ∈ Icc (0 : ℝ) r,
      F (if vertical then (0, s) else (s, 0)) = gamma (if terminal then T - s else s)) :
    ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ gamma (if terminal then T - r else r) ∈ W ∧
      ell (deriv gamma (if terminal then T - r else r)) = (if terminal then -1 else 1) ∧
      ell (if vertical then F (r, 0) - F (0, r) else F (0, r) - F (r, 0)) = 0 ∧
      ∀ z ∈ W ∩ F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r},
        ell (z - gamma (if terminal then T - r else r)) ≤ 0 := by
  let b : ℝ → AnnulusCoordinates := fun s => F (if vertical then (0, s) else (s, 0))
  let beta : ℝ → AnnulusCoordinates := fun s => gamma (if terminal then T - s else s)
  have hrI : r ∈ Icc (0 : ℝ) r := ⟨hr.le, le_rfl⟩
  have hbs : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ F.source := by
    apply hsource
    cases vertical <;> simp [hr.le]
  have hb : DifferentiableAt ℝ b r := by
    have hdF := (hF.contDiffAt (F.open_source.mem_nhds hbs)).differentiableAt (by simp)
    cases vertical
    · exact hdF.comp r (differentiableAt_id.prodMk (differentiableAt_const (0 : ℝ)))
    · exact hdF.comp r ((differentiableAt_const (0 : ℝ)).prodMk differentiableAt_id)
  have hbeta : ContDiff ℝ ∞ beta := by
    cases terminal
    · exact hg
    · exact hg.comp (contDiff_const.sub contDiff_id)
  have hderiv : deriv b r = deriv beta r := by
    rw [← hb.derivWithin (uniqueDiffOn_Icc hr r hrI),
      ← ((hbeta.differentiable (by simp)) r).derivWithin (uniqueDiffOn_Icc hr r hrI)]
    exact derivWithin_congr haxis (haxis r hrI)
  obtain ⟨ell, W, hnorm, hker, hW, hpW, _, hbound⟩ :=
    exists_cap_chord_separator F hF hFi hr hsource hchord vertical
  have hbase : (if vertical then F (0, r) else F (r, 0)) =
      gamma (if terminal then T - r else r) := by
    cases vertical <;> exact haxis r hrI
  have hnorm' : ell (deriv b r) = 1 := by cases vertical <;> exact hnorm
  rw [hderiv] at hnorm'
  refine ⟨ell, W, hW, hbase ▸ hpW, ?_, hker, ?_⟩
  · cases terminal
    · exact hnorm'
    · simp only [beta, ite_true, deriv_comp_const_sub, map_neg] at hnorm'
      dsimp
      linarith
  · intro z hz
    simpa only [hbase] using hbound z hz

end PoincareConjecture
