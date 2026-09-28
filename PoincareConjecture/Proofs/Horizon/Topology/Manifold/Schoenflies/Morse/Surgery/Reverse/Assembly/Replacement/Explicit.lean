import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.Asymmetric
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.CapRange
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.MarkedEquivalence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.LensNesting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Protected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem exists_explicit_lower_replacement
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fMinus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fPlus)) :
    ∃ (u : Real) (hu : 0 < u), u < S.s ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        F '' range (fun p => S.D (f p)) =
          (liftPlaneDiffeomorph S.unit_v (c - S.a) (-u) (neg_ne_zero.mpr hu.ne') S.A ''
            boundedCylinderNorthernCap v) ∪
          {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
            (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
          ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) := by
  obtain ⟨g, r, η, hg, hgi, hgd, hr, hr', hrη, hcore, hsub, hcollar⟩ :=
    S.exists_capMinus_collar_in_child
  obtain ⟨d, hd, L, hdclock, hsd, hdabs, _, hLmark, hstrict, hbound, hcomplement⟩ :=
    Reverse.exists_asymmetric_cap_lens S.unit_v (c - S.a) S.s S.s_pos.ne' S.A S.γ
      S.circle_image g hgi (hcore.trans S.gMinus_range) hr hr'.le hrη hcollar
  have hdneg : d < 0 := by
    rw [hdclock]
    exact mul_neg_of_pos_of_neg S.s_pos (Reverse.capCollarClock_neg_of_one_lt hr)
  have hdsmall : -d < S.s := by
    rwa [abs_of_neg hdneg, abs_of_pos S.s_pos] at hdabs
  have hbound' : ∀ y ∈ L '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1 ∧
      |inner Real v y - (c - S.a)| ≤ 2 * S.s := by
    simpa only [abs_of_pos S.s_pos] using hbound
  have hmeet := Reverse.lens_inter_replacement_eq_marked_disk (c - S.a) S.s S.A L g hr.le
    ((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) hLmark
    (by rw [hcore, ← S.fMinus_range]; exact hsub) hstrict hbound (by
      rintro y ⟨p, _, rfl⟩ hproj hh
      apply S.projection_mem_circle_of_mem_prepared (mem_range_self p) hproj
      rw [abs_of_pos S.s_pos] at hh
      obtain ⟨hl, hu⟩ := abs_le.mp hh
      exact abs_le.mpr ⟨by linarith [S.s_lt_eighth_a, S.a_pos],
        by linarith [S.s_lt_eighth_a, S.a_pos]⟩)
  rw [hcore, ← S.fMinus_range] at hmeet
  have hnest := S.capMinus_lens_subset_filling B L hB havoid g hg hgi hgd hr hcore hsub
    hLmark hmeet hbound'
  obtain ⟨D, hDB, hDfix⟩ := Reverse.exists_ball_equivalence_fixing_common_disk B L g hg hgi hgd
    (zero_lt_one.trans hr) (hB.symm ▸ hsub) hLmark ⟨v, mem_sphere_zero_iff_norm.mpr S.unit_v⟩
  obtain ⟨F, hchild, hcap, hannulus, hother⟩ := S.exists_protected_lower_replacement B L D
    hB havoid hDB hnest g hg hgi hgd hr hcore hsub hDfix
  have hfull := S.image_prepared_range_of_lower_replacement F L hchild hcap hannulus hother
  have hopen := S.open_capMinus_range_of_collar g hgi hcore (by linarith : 0 < η) hcollar
  rw [hopen] at hcomplement
  rw [hcomplement] at hfull
  exact ⟨-d, neg_pos.mpr hdneg, hdsmall, F, by simpa only [neg_neg] using hfull⟩

theorem exists_explicit_upper_replacement
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fPlus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fMinus)) :
    ∃ (u : Real) (hu : 0 < u), u < S.s ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        F '' range (fun p => S.D (f p)) =
          ((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) ∪
          {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
            (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
          (liftPlaneDiffeomorph S.unit_v (c + S.a) u hu.ne' S.A ''
            boundedCylinderNorthernCap v) := by
  obtain ⟨g, r, η, hg, hgi, hgd, hr, hr', hrη, hcore, hsub, hcollar⟩ :=
    S.exists_capPlus_collar_in_child
  obtain ⟨d, hd, L, hdclock, hsd, hdabs, _, hLmark, hstrict, hbound, hcomplement⟩ :=
    Reverse.exists_asymmetric_cap_lens S.unit_v (c + S.a) (-S.s) (neg_ne_zero.mpr S.s_pos.ne')
      S.A S.γ S.circle_image g hgi (hcore.trans S.gPlus_range) hr hr'.le hrη hcollar
  have hdpos : 0 < d := by
    rw [hdclock]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos S.s_pos) (Reverse.capCollarClock_neg_of_one_lt hr)
  have hdsmall : d < S.s := by
    rwa [abs_of_pos hdpos, abs_neg, abs_of_pos S.s_pos] at hdabs
  have hbound' : ∀ y ∈ L '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1 ∧
      |inner Real v y - (c + S.a)| ≤ 2 * S.s := by
    simpa only [abs_neg, abs_of_pos S.s_pos] using hbound
  have hmeet := Reverse.lens_inter_replacement_eq_marked_disk (c + S.a) (-S.s) S.A L g hr.le
    ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) hLmark
    (by rw [hcore, ← S.fPlus_range]; exact hsub) hstrict hbound (by
      rintro y ⟨p, _, rfl⟩ hproj hh
      apply S.projection_mem_circle_of_mem_prepared (mem_range_self p) hproj
      rw [abs_neg, abs_of_pos S.s_pos] at hh
      obtain ⟨hl, hu⟩ := abs_le.mp hh
      exact abs_le.mpr ⟨by linarith [S.s_lt_eighth_a, S.a_pos],
        by linarith [S.s_lt_eighth_a, S.a_pos]⟩)
  rw [hcore, ← S.fPlus_range] at hmeet
  have hnest := S.capPlus_lens_subset_filling B L hB havoid g hg hgi hgd hr hcore hsub
    hLmark hmeet hbound'
  obtain ⟨D, hDB, hDfix⟩ := Reverse.exists_ball_equivalence_fixing_common_disk B L g hg hgi hgd
    (zero_lt_one.trans hr) (hB.symm ▸ hsub) hLmark ⟨v, mem_sphere_zero_iff_norm.mpr S.unit_v⟩
  obtain ⟨F, hchild, hcap, hannulus, hother⟩ := S.exists_protected_upper_replacement B L D
    hB havoid hDB hnest g hg hgi hgd hr hcore hsub hDfix
  have hfull := S.image_prepared_range_of_upper_replacement F L hchild hcap hannulus hother
  have hopen := S.open_capPlus_range_of_collar g hgi hcore (by linarith : 0 < η) hcollar
  rw [hopen] at hcomplement
  rw [hcomplement] at hfull
  exact ⟨d, hdpos, hdsmall, F, hfull⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryStep
