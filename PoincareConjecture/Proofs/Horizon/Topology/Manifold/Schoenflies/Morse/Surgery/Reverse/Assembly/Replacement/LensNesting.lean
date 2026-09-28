import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Placement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Annulus.Clearance



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

namespace Reverse



theorem not_mem_open_body_of_projection_mem_circle
    {v : E3} (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hbound : ∀ y ∈ L '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1)
    {y : E3} (hcircle : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1) :
    y ∉ L '' ball (0 : E3) 1 := by
  intro hy
  have hproj := projection_mem_open_disk_of_mem_open_body A L.toHomeomorph hbound hy
  obtain ⟨x, hx, hxy⟩ := hproj
  obtain ⟨z, hz, hzy⟩ := hcircle
  have hxz : x = z := A.injective (hxy.trans hzy.symm)
  rw [hxz] at hx
  exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)

end Reverse

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)




theorem capMinus_lens_subset_filling
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fMinus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fPlus))
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hcore : g '' closedBall (0 : E2) 1 = S.gMinus '' closedBall 0 1)
    (hBmark : g '' closedBall (0 : E2) r ⊆ range S.fMinus)
    (hLmark : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    (hmeet : (L '' sphere (0 : E3) 1) ∩ range S.fMinus = g '' closedBall (0 : E2) r)
    (hbound : ∀ y ∈ L '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1 ∧
      |inner Real v y - (c - S.a)| ≤ 2 * S.s) :
    L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 := by
  have hplace := Reverse.lens_filled_placement_of_clearance S.A B L
    (S.gMinus '' closedBall 0 1) ((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1))
    (c - S.a) (2 * S.s) (hB.trans S.fMinus_range)
    (by rw [← hcore]; exact (image_mono (closedBall_subset_closedBall hr.le)).trans hLmark)
    hbound (by
      rintro y ⟨p, _, rfl⟩ hproj hh
      apply S.projection_mem_circle_of_mem_prepared (mem_range_self p) hproj
      obtain ⟨hl, hu⟩ := abs_le.mp hh
      exact abs_le.mpr ⟨by linarith [S.s_lt_eighth_a, S.a_pos],
        by linarith [S.s_lt_eighth_a, S.a_pos]⟩)
  have hplace' : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
      (B '' closedBall (0 : E3) 1) ∩ (L '' closedBall (0 : E3) 1) =
        g '' closedBall (0 : E2) r := by
    simpa only [hB, inter_comm (range S.fMinus), hmeet] using hplace
  obtain ⟨q0, hq0⟩ := (NormedSpace.sphere_nonempty (x := (0 : E2))).mpr
    (show (0 : Real) ≤ 1 by norm_num)
  let q : S1 := ⟨q0, hq0⟩
  let line : Real → E3 := fun t => (c + t) • v + (S.γ q : E3)
  let C := line '' Ioo (-S.a + S.s) S.a
  have htop : -S.a + S.s ∈ Ioo (-S.ε) S.ε :=
    ⟨by linarith [S.a_lt_quarter_ε, S.s_pos, S.a_pos],
      by linarith [S.a_lt_quarter_ε, S.s_lt_eighth_a, S.a_pos]⟩
  have hpcap : line (-S.a + S.s) ∈ g '' closedBall (0 : E2) 1 := by
    rw [hcore]
    change (c + (-S.a + S.s)) • v + (S.γ q : E3) ∈ _
    rw [← S.cylinder q _ htop]
    exact (S.prepared_tube_mem_capMinus_iff q htop).mpr
      ⟨by linarith [S.s_pos], le_rfl⟩
  have hpcl : line (-S.a + S.s) ∈ closure C := by
    have hc : Continuous line := (continuous_const.add continuous_id).smul continuous_const
      |>.add continuous_const
    apply hc.continuousWithinAt.mem_closure_image
    rw [closure_Ioo (by linarith [S.s_lt_eighth_a, S.a_pos] : -S.a + S.s ≠ S.a)]
    exact ⟨le_rfl, by linarith [S.s_lt_eighth_a, S.a_pos]⟩
  apply Reverse.filled_ball_subset_of_shared_exterior_at_cap B L g hg hgi hgd hr
    (hB.symm ▸ hBmark) hLmark hplace' hpcap hpcl
  · rintro y ⟨t, ht, rfl⟩
    have hte : t ∈ Ioo (-S.ε) S.ε :=
      ⟨htop.1.trans ht.1, by linarith [ht.2, S.a_lt_quarter_ε, S.a_pos]⟩
    change line t ∉ B '' closedBall (0 : E3) 1
    rw [show line t = S.D (f (S.T (q, t))) from (S.cylinder q t hte).symm]
    exact S.prepared_tube_not_mem_filledMinus B hB havoid q ht.1 ht.2.le
  · rintro y ⟨t, _, rfl⟩
    apply Reverse.not_mem_open_body_of_projection_mem_circle S.A L
      (fun y hy => (hbound y hy).1)
    have hc : S.γ q ∈ S.A '' sphere (0 : Hemisphere.Plane v) 1 := by
      rw [S.circle_image]
      exact mem_range_self q
    simpa [line, Hemisphere.Plane,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero] using hc
  · exact ⟨v, mem_sphere_zero_iff_norm.mpr S.unit_v⟩


theorem capPlus_lens_subset_filling
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fPlus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fMinus))
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hcore : g '' closedBall (0 : E2) 1 = S.gPlus '' closedBall 0 1)
    (hBmark : g '' closedBall (0 : E2) r ⊆ range S.fPlus)
    (hLmark : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    (hmeet : (L '' sphere (0 : E3) 1) ∩ range S.fPlus = g '' closedBall (0 : E2) r)
    (hbound : ∀ y ∈ L '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1 ∧
      |inner Real v y - (c + S.a)| ≤ 2 * S.s) :
    L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 := by
  have hplace := Reverse.lens_filled_placement_of_clearance S.A B L
    (S.gPlus '' closedBall 0 1) ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1))
    (c + S.a) (2 * S.s) (hB.trans S.fPlus_range)
    (by rw [← hcore]; exact (image_mono (closedBall_subset_closedBall hr.le)).trans hLmark)
    hbound (by
      rintro y ⟨p, _, rfl⟩ hproj hh
      apply S.projection_mem_circle_of_mem_prepared (mem_range_self p) hproj
      obtain ⟨hl, hu⟩ := abs_le.mp hh
      exact abs_le.mpr ⟨by linarith [S.s_lt_eighth_a, S.a_pos],
        by linarith [S.s_lt_eighth_a, S.a_pos]⟩)
  have hplace' : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
      (B '' closedBall (0 : E3) 1) ∩ (L '' closedBall (0 : E3) 1) =
        g '' closedBall (0 : E2) r := by
    simpa only [hB, inter_comm (range S.fPlus), hmeet] using hplace
  obtain ⟨q0, hq0⟩ := (NormedSpace.sphere_nonempty (x := (0 : E2))).mpr
    (show (0 : Real) ≤ 1 by norm_num)
  let q : S1 := ⟨q0, hq0⟩
  let line : Real → E3 := fun t => (c + t) • v + (S.γ q : E3)
  let C := line '' Ioo (-S.a) (S.a - S.s)
  have htop : S.a - S.s ∈ Ioo (-S.ε) S.ε :=
    ⟨by linarith [S.a_lt_quarter_ε, S.s_lt_eighth_a, S.a_pos],
      by linarith [S.a_lt_quarter_ε, S.s_pos, S.a_pos]⟩
  have hpcap : line (S.a - S.s) ∈ g '' closedBall (0 : E2) 1 := by
    rw [hcore]
    change (c + (S.a - S.s)) • v + (S.γ q : E3) ∈ _
    rw [← S.cylinder q _ htop]
    exact (S.prepared_tube_mem_capPlus_iff q htop).mpr
      ⟨le_rfl, by linarith [S.s_pos]⟩
  have hpcl : line (S.a - S.s) ∈ closure C := by
    have hc : Continuous line := (continuous_const.add continuous_id).smul continuous_const
      |>.add continuous_const
    apply hc.continuousWithinAt.mem_closure_image
    rw [closure_Ioo (by linarith [S.s_lt_eighth_a, S.a_pos] : -S.a ≠ S.a - S.s)]
    exact ⟨by linarith [S.s_lt_eighth_a, S.a_pos], le_rfl⟩
  apply Reverse.filled_ball_subset_of_shared_exterior_at_cap B L g hg hgi hgd hr
    (hB.symm ▸ hBmark) hLmark hplace' hpcap hpcl
  · rintro y ⟨t, ht, rfl⟩
    have hte : t ∈ Ioo (-S.ε) S.ε :=
      ⟨by linarith [ht.1, S.a_lt_quarter_ε, S.a_pos], ht.2.trans htop.2⟩
    change line t ∉ B '' closedBall (0 : E3) 1
    rw [show line t = S.D (f (S.T (q, t))) from (S.cylinder q t hte).symm]
    exact S.prepared_tube_not_mem_filledPlus B hB havoid q ht.1.le ht.2
  · rintro y ⟨t, _, rfl⟩
    apply Reverse.not_mem_open_body_of_projection_mem_circle S.A L
      (fun y hy => (hbound y hy).1)
    have hc : S.γ q ∈ S.A '' sphere (0 : Hemisphere.Plane v) 1 := by
      rw [S.circle_image]
      exact mem_range_self q
    simpa [line, Hemisphere.Plane,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero] using hc
  · exact ⟨v, mem_sphere_zero_iff_norm.mpr S.unit_v⟩

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
