import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Correction.CapBelt

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem cap_boundary_image
    (f f' : S2 → E3) (g : E2 → E3) (d e : OpenPartialHomeomorph E2 S2)
    (hds : closedBall (0 : E2) 1 ⊆ d.source)
    (hes : closedBall (0 : E2) 1 ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hdclosed : d '' closedBall (0 : E2) 1 = (e '' ball (0 : E2) 1)ᶜ)
    (hpatch : ∀ x ∈ closedBall (0 : E2) 1, f' (d x) = g x)
    (hretained : ∀ p ∈ e '' closedBall (0 : E2) 1, f' p = f p) :
    g '' sphere (0 : E2) 1 = f '' (e '' sphere (0 : E2) 1) := by
  have hde : d '' sphere (0 : E2) 1 = e '' sphere (0 : E2) 1 := by
    rw [d.image_sphere_eq_frontier hds rfl, hdclosed, frontier_compl,
      ParallelDisks.frontier_image_ball zero_lt_one e hes he hei]
  calc
    g '' sphere (0 : E2) 1 = f' '' (d '' sphere (0 : E2) 1) := by
      rw [image_image]
      exact image_congr fun x hx => (hpatch x (sphere_subset_closedBall hx)).symm
    _ = f' '' (e '' sphere (0 : E2) 1) := by rw [hde]
    _ = f '' (e '' sphere (0 : E2) 1) := image_congr fun p hp =>
      hretained p ((image_mono sphere_subset_closedBall) hp)

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem capMinus_edge_eq_cutting_circle :
    S.gMinus '' sphere (0 : E2) 1 =
      range (fun q : S1 => (c - S.a) • v + (S.γ q : E3)) := by
  rw [cap_boundary_image (fun p => S.D (f p)) S.fMinus S.gMinus S.dMinus S.eMinus
    S.dMinus_source S.eMinus_source S.eMinus_smooth S.eMinus_symm_smooth
    S.dMinus_closed S.capMinus_eq S.retainedMinus_eq, S.eMinus_boundary, ← range_comp]
  apply congrArg range
  funext q
  change S.D (f (S.T (q, -S.a))) = (c - S.a) • v + (S.γ q : E3)
  rw [sub_eq_add_neg]
  exact S.cylinder q (-S.a)
    ⟨by linarith [S.a_lt_quarter_ε, S.a_pos], by linarith [S.ε_pos, S.a_pos]⟩

theorem capPlus_edge_eq_cutting_circle :
    S.gPlus '' sphere (0 : E2) 1 =
      range (fun q : S1 => (c + S.a) • v + (S.γ q : E3)) := by
  rw [cap_boundary_image (fun p => S.D (f p)) S.fPlus S.gPlus S.dPlus S.ePlus
    S.dPlus_source S.ePlus_source S.ePlus_smooth S.ePlus_symm_smooth
    S.dPlus_closed S.capPlus_eq S.retainedPlus_eq, S.ePlus_boundary, ← range_comp]
  apply congrArg range
  funext q
  exact S.cylinder q S.a
    ⟨by linarith [S.ε_pos, S.a_pos], by linarith [S.a_lt_quarter_ε, S.a_pos]⟩

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
