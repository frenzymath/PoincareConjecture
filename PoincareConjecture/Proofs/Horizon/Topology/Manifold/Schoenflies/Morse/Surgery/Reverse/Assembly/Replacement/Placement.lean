import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.FilledSides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.CommonDisk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Marking

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem lens_filled_placement_of_clearance
    {v : E3} (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (cap retained : Set E3) (b h : Real)
    (hboundary : B '' sphere (0 : E3) 1 = cap ∪ retained)
    (hcap : cap ⊆ L '' sphere (0 : E3) 1)
    (hbound : ∀ y ∈ L '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
      |inner Real v y - b| ≤ h)
    (hclear : ∀ y ∈ retained,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 →
      |inner Real v y - b| ≤ h →
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1) :
    L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
      (B '' closedBall (0 : E3) 1) ∩ (L '' closedBall (0 : E3) 1) =
        (B '' sphere (0 : E3) 1) ∩ (L '' sphere (0 : E3) 1) := by
  apply filled_ball_subset_or_inter_eq_boundary B.toHomeomorph L.toHomeomorph
  apply disjoint_left.mpr
  intro y hyL hyB
  have hyLc := (image_mono ball_subset_closedBall) hyL
  have hproj := projection_mem_open_disk_of_mem_open_body A L.toHomeomorph
    (fun z hz => (hbound z hz).1) hyL
  change y ∈ B '' sphere (0 : E3) 1 at hyB
  rw [hboundary] at hyB
  rcases hyB with hycap | hyretained
  · obtain ⟨x, hx, hxy⟩ := hcap hycap
    obtain ⟨z, hz, hzy⟩ := hyL
    have hxz : x = z := L.injective (hxy.trans hzy.symm)
    rw [hxz] at hx
    exact (ne_of_lt (mem_ball_zero_iff.mp hz)) (mem_sphere_zero_iff_norm.mp hx)
  · have hcircle := hclear y hyretained (hbound y hyLc).1 (hbound y hyLc).2
    obtain ⟨x, hx, hxy⟩ := hproj
    obtain ⟨z, hz, hzy⟩ := hcircle
    have hxz : x = z := A.injective (hxy.trans hzy.symm)
    rw [hxz] at hx
    exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)

theorem filled_ball_subset_of_shared_exterior
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (m n : E2 → S2) {x : E2} (hx : x ∈ ball 0 1)
    (hml : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x)
    (hnl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ n x)
    (hmark : ∀ z ∈ closedBall (0 : E2) 1, B (m z : E3) = L (n z : E3))
    (hplacement : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
      (B '' closedBall (0 : E3) 1) ∩ (L '' closedBall (0 : E3) 1) =
        (fun z => B (m z : E3)) '' closedBall (0 : E2) 1)
    {C : Set E3} (hp : B (m x : E3) ∈ closure C)
    (hCB : C ⊆ (B '' closedBall (0 : E3) 1)ᶜ)
    (hCL : C ⊆ (L '' ball (0 : E3) 1)ᶜ) :
    L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 := by
  rcases hplacement with hin | hmeet
  · exact hin
  obtain ⟨W, hW, hpW, hside⟩ :=
    Rounding.CommonDisk.exists_opposite_filled_sides B L m n hx hml hnl hmark hmeet
  obtain ⟨y, hyW, hyC⟩ := mem_closure_iff.mp hp W hW hpW
  have hyB : y ∈ B '' closedBall (0 : E3) 1 :=
    (hside.symm ▸ (show y ∈ W ∩ (L '' ball (0 : E3) 1)ᶜ from ⟨hyW, hCL hyC⟩)).2
  exact False.elim (hCB hyC hyB)

theorem filled_ball_subset_of_shared_exterior_at_cap
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hBmark : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hLmark : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    (hplacement : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
      (B '' closedBall (0 : E3) 1) ∩ (L '' closedBall (0 : E3) 1) =
        g '' closedBall (0 : E2) r)
    {C : Set E3} {p : E3} (hp : p ∈ g '' closedBall (0 : E2) 1)
    (hpcl : p ∈ closure C)
    (hCB : C ⊆ (B '' closedBall (0 : E3) 1)ᶜ)
    (hCL : C ⊆ (L '' ball (0 : E3) 1)ᶜ)
    (p0 : S2) :
    L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 := by
  obtain ⟨m, hmi, hml, hm, hmrange⟩ := exists_ambient_disk_marking_at_radius B g hg hgi hgd
    (zero_lt_one.trans hr) hBmark p0
  obtain ⟨n, hni, hnl, hn, _⟩ := exists_ambient_disk_marking_at_radius L g hg hgi hgd
    (zero_lt_one.trans hr) hLmark p0
  obtain ⟨z, hz, rfl⟩ := hp
  let x : E2 := r⁻¹ • z
  have hx : x ∈ ball (0 : E2) 1 := by
    rw [mem_ball_zero_iff]
    change ‖r⁻¹ • z‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (zero_lt_one.trans hr))]
    calc
      r⁻¹ * ‖z‖ ≤ r⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz)
          (inv_nonneg.mpr (zero_lt_one.trans hr).le)
      _ < 1 := by simpa using (inv_lt_one₀ (zero_lt_one.trans hr)).mpr hr
  have hrx : r • x = z := by
    dsimp [x]
    rw [smul_smul, mul_inv_cancel₀ (zero_lt_one.trans hr).ne', one_smul]
  have hmp : B (m x : E3) = g z := by rw [hm x (ball_subset_closedBall hx), hrx]
  apply filled_ball_subset_of_shared_exterior B L m n hx
    (hml x (ball_subset_closedBall hx)) (hnl x (ball_subset_closedBall hx))
      (fun y hy => (hm y hy).trans (hn y hy).symm)
  · rwa [hmrange]
  · rwa [hmp]
  · exact hCB
  · exact hCL

end Poincare.Manifold.Schoenflies.Reverse
