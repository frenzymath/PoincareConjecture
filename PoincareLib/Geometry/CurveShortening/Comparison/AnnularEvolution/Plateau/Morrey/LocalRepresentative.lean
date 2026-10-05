import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Morrey.LocalRescaling
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Morrey.LocalPatching

/-!
# The actual continuous representative from local Morrey growth

On an arbitrary planar domain, local power bounds for genuine weak
columns produce local continuous representatives by rescaling. Their
almost-everywhere identification patches them into one continuous map
on the whole domain. No representative regularity is assumed.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Local all-centers column energy growth constructs an actual continuous representative on
the full planar domain. The local closed disk inclusion already implies that the domain is
open. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Morrey_local_representative {m : ℕ} {O : Set Plane}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => V i y b) (fun y => u y b) O)
    (hgrowth : ∀ a ∈ O, ∃ rho : ℝ, 0 < rho ∧ closedBall a (2 * rho) ⊆ O ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∃ beta : ℝ, 0 < beta ∧
        ∀ i : Fin 2, ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho,
          (∫ y in ball b r, ‖V i y‖ ^ 2) ≤ K * r ^ beta) :
    ∃ U : Plane → EuclideanSpace ℝ (Fin m),
      ContinuousOn U O ∧ U =ᵐ[volume.restrict O] u := by
  apply m64Morrey_patch_representatives
  intro a ha
  obtain ⟨rho, hrho, hsub, K, hK, beta, hbeta, henergy⟩ := hgrowth a ha
  have hsub2 : ball a (rho * 2) ⊆ O := by
    rw [mul_comm rho 2]
    exact ball_subset_closedBall.trans hsub
  obtain ⟨U, hU, hUae⟩ := m64Morrey_local_disk_representative hrho
    (hu.mono_measure (Measure.restrict_mono hsub2 le_rfl))
    (fun i => (hV i).mono_measure (Measure.restrict_mono hsub2 le_rfl))
    (fun i b => (hw i b).restrict isOpen_ball hsub2) hK hbeta henergy
  refine ⟨ball a (rho / 2), isOpen_ball, mem_ball_self (half_pos hrho), ?_,
    U, hU.mono ball_subset_closedBall, hUae⟩
  exact (ball_subset_ball (by linarith : rho / 2 ≤ rho * 2)).trans hsub2

end PoincareMT
