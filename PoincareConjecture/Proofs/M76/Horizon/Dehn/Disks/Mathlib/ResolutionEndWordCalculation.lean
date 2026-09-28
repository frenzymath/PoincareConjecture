import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionRimWords

set_option autoImplicit false

namespace PoincareConjecture.M76.Dehn

variable {X : Type*} [TopologicalSpace X]
  {b z0 z1 a0 a1 c0 c1 l0 l1 r0 r1 : X}

theorem resolution_end_words_case_a
    (p : Path b z0) (q : Path b z1)
    (ra0 : Path z0 a0) (rc0 : Path z0 c0) (rl0 : Path z0 l0) (rr0 : Path z0 r0)
    (ra1 : Path z1 a1) (rc1 : Path z1 c1) (rl1 : Path z1 l1) (rr1 : Path z1 r1)
    (U0 : Path a0 c0) (L0 : Path l0 a0) (R0 : Path r0 c0)
    (U1 : Path a1 c1) (L1 : Path l1 a1) (R1 : Path r1 c1)
    (hU0 : U0.Homotopic (ra0.symm.trans rc0))
    (hL0 : L0.Homotopic (rl0.symm.trans ra0))
    (hR0 : R0.Homotopic (rr0.symm.trans rc0))
    (hU1 : U1.Homotopic (ra1.symm.trans rc1))
    (hL1 : L1.Homotopic (rl1.symm.trans ra1))
    (hR1 : R1.Homotopic (rr1.symm.trans rc1))
    (a : Path a0 a1) (β : Path r1 l1) (c : Path c1 c0) (d : Path l0 r0) :
    let A := basedPathWord (p.trans ra0) (q.trans ra1) a
    let B := basedPathWord (q.trans rr1) (q.trans rl1) β
    let C := basedPathWord (q.trans rc1) (p.trans rc0) c
    let D := basedPathWord (p.trans rl0) (p.trans rr0) d
    basedPathWord (p.trans ra0) (p.trans ra0)
        (((a.trans U1).trans c).trans U0.symm) = A * C ∧
      basedPathWord (p.trans ra0) (p.trans ra0)
        (((((((a.trans L1.symm).trans β.symm).trans R1).trans c).trans R0.symm).trans
          d.symm).trans L0) = A * B⁻¹ * C * D⁻¹ := by
  dsimp only
  have hu0 := basedPathWord_end_path p ra0 rc0 U0 hU0
  have hl0 := basedPathWord_end_path p rl0 ra0 L0 hL0
  have hr0 := basedPathWord_end_path p rr0 rc0 R0 hR0
  have hu1 := basedPathWord_end_path q ra1 rc1 U1 hU1
  have hl1 := basedPathWord_end_path q rl1 ra1 L1 hL1
  have hr1 := basedPathWord_end_path q rr1 rc1 R1 hR1
  constructor
  · rw [basedPathWord_trans (p.trans ra0) (p.trans rc0) (p.trans ra0),
      basedPathWord_trans (p.trans ra0) (q.trans rc1) (p.trans rc0),
      basedPathWord_trans (p.trans ra0) (q.trans ra1) (q.trans rc1),
      basedPathWord_symm, hu0, hu1, inv_one, mul_one, mul_one]
  · rw [basedPathWord_trans (p.trans ra0) (p.trans rl0) (p.trans ra0),
      basedPathWord_trans (p.trans ra0) (p.trans rr0) (p.trans rl0),
      basedPathWord_trans (p.trans ra0) (p.trans rc0) (p.trans rr0),
      basedPathWord_trans (p.trans ra0) (q.trans rc1) (p.trans rc0),
      basedPathWord_trans (p.trans ra0) (q.trans rr1) (q.trans rc1),
      basedPathWord_trans (p.trans ra0) (q.trans rl1) (q.trans rr1),
      basedPathWord_trans (p.trans ra0) (q.trans ra1) (q.trans rl1)]
    simp only [basedPathWord_symm, hl0, hr0, hl1, hr1, inv_one, mul_one]

theorem resolution_end_words_case_b
    (p : Path b z0) (q : Path b z1)
    (ra0 : Path z0 a0) (rc0 : Path z0 c0) (rl0 : Path z0 l0) (rr0 : Path z0 r0)
    (ra1 : Path z1 a1) (rc1 : Path z1 c1) (rl1 : Path z1 l1) (rr1 : Path z1 r1)
    (U0 : Path a0 c0) (L0 : Path l0 a0) (R0 : Path r0 c0)
    (U1 : Path a1 c1) (L1 : Path l1 a1) (R1 : Path r1 c1)
    (hU0 : U0.Homotopic (ra0.symm.trans rc0))
    (hL0 : L0.Homotopic (rl0.symm.trans ra0))
    (hR0 : R0.Homotopic (rr0.symm.trans rc0))
    (hU1 : U1.Homotopic (ra1.symm.trans rc1))
    (hL1 : L1.Homotopic (rl1.symm.trans ra1))
    (hR1 : R1.Homotopic (rr1.symm.trans rc1))
    (a : Path a1 a0) (β : Path r0 l1) (c : Path c1 c0) (d : Path l0 r1) :
    let A := basedPathWord (q.trans ra1) (p.trans ra0) a
    let B := basedPathWord (p.trans rr0) (q.trans rl1) β
    let C := basedPathWord (q.trans rc1) (p.trans rc0) c
    let D := basedPathWord (p.trans rl0) (q.trans rr1) d
    basedPathWord (q.trans ra1) (q.trans ra1)
        (((a.trans U0).trans c.symm).trans U1.symm) = A * C⁻¹ ∧
      basedPathWord (q.trans ra1) (q.trans ra1)
        (((((((a.trans L0.symm).trans d).trans R1).trans c).trans R0.symm).trans
          β).trans L1) = A * D * C * B := by
  dsimp only
  have hu0 := basedPathWord_end_path p ra0 rc0 U0 hU0
  have hl0 := basedPathWord_end_path p rl0 ra0 L0 hL0
  have hr0 := basedPathWord_end_path p rr0 rc0 R0 hR0
  have hu1 := basedPathWord_end_path q ra1 rc1 U1 hU1
  have hl1 := basedPathWord_end_path q rl1 ra1 L1 hL1
  have hr1 := basedPathWord_end_path q rr1 rc1 R1 hR1
  constructor
  · rw [basedPathWord_trans (q.trans ra1) (q.trans rc1) (q.trans ra1),
      basedPathWord_trans (q.trans ra1) (p.trans rc0) (q.trans rc1),
      basedPathWord_trans (q.trans ra1) (p.trans ra0) (p.trans rc0)]
    simp only [basedPathWord_symm, hu0, hu1, inv_one, mul_one]
  · rw [basedPathWord_trans (q.trans ra1) (q.trans rl1) (q.trans ra1),
      basedPathWord_trans (q.trans ra1) (p.trans rr0) (q.trans rl1),
      basedPathWord_trans (q.trans ra1) (p.trans rc0) (p.trans rr0),
      basedPathWord_trans (q.trans ra1) (q.trans rc1) (p.trans rc0),
      basedPathWord_trans (q.trans ra1) (q.trans rr1) (q.trans rc1),
      basedPathWord_trans (q.trans ra1) (p.trans rl0) (q.trans rr1),
      basedPathWord_trans (q.trans ra1) (p.trans ra0) (p.trans rl0)]
    simp only [basedPathWord_symm, hl0, hr0, hl1, hr1, inv_one, mul_one]

theorem resolution_end_excluded_case_a
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b z0) (q : Path b z1)
    (ra0 : Path z0 a0) (rc0 : Path z0 c0) (rl0 : Path z0 l0) (rr0 : Path z0 r0)
    (ra1 : Path z1 a1) (rc1 : Path z1 c1) (rl1 : Path z1 l1) (rr1 : Path z1 r1)
    (U0 : Path a0 c0) (L0 : Path l0 a0) (R0 : Path r0 c0)
    (U1 : Path a1 c1) (L1 : Path l1 a1) (R1 : Path r1 c1)
    (hU0 : U0.Homotopic (ra0.symm.trans rc0))
    (hL0 : L0.Homotopic (rl0.symm.trans ra0))
    (hR0 : R0.Homotopic (rr0.symm.trans rc0))
    (hU1 : U1.Homotopic (ra1.symm.trans rc1))
    (hL1 : L1.Homotopic (rl1.symm.trans ra1))
    (hR1 : R1.Homotopic (rr1.symm.trans rc1))
    (a : Path a0 a1) (β : Path r1 l1) (c : Path c1 c0) (d : Path l0 r0)
    (hold : p.whiskeredLoopClass
      (((((ra0.trans a).trans ra1.symm).trans ((rr1.trans β).trans rl1.symm)).trans
        ((rc1.trans c).trans rc0.symm)).trans ((rl0.trans d).trans rr0.symm)) ∉ J) :
    (p.trans ra0).whiskeredLoopClass (((a.trans U1).trans c).trans U0.symm) ∉ J ∨
      (p.trans ra0).whiskeredLoopClass
        (((((((a.trans L1.symm).trans β.symm).trans R1).trans c).trans R0.symm).trans
          d.symm).trans L0) ∉ J := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hFirst, hSecond⟩ := resolution_end_words_case_a p q
    ra0 rc0 rl0 rr0 ra1 rc1 rl1 rr1 U0 L0 R0 U1 L1 R1
    hU0 hL0 hR0 hU1 hL1 hR1 a β c d
  have hOld := (resolution_words_case_a p q
    ((ra0.trans a).trans ra1.symm) ((rc1.trans c).trans rc0.symm)
    ((rl0.trans d).trans rr0.symm) ((rr1.trans β).trans rl1.symm)).1
  rw [← basedPathWord_radial, ← basedPathWord_radial,
    ← basedPathWord_radial, ← basedPathWord_radial] at hOld
  apply hold
  apply J.inv_mem_iff.mp
  change basedPathWord p p _ ∈ J
  rw [hOld]
  apply old_word_mem_of_case_a J
  · rw [← hFirst, basedPathWord_loop]
    exact J.inv_mem h.1
  · rw [← hSecond, basedPathWord_loop]
    exact J.inv_mem h.2

theorem resolution_end_excluded_case_b
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b z0) (q : Path b z1)
    (ra0 : Path z0 a0) (rc0 : Path z0 c0) (rl0 : Path z0 l0) (rr0 : Path z0 r0)
    (ra1 : Path z1 a1) (rc1 : Path z1 c1) (rl1 : Path z1 l1) (rr1 : Path z1 r1)
    (U0 : Path a0 c0) (L0 : Path l0 a0) (R0 : Path r0 c0)
    (U1 : Path a1 c1) (L1 : Path l1 a1) (R1 : Path r1 c1)
    (hU0 : U0.Homotopic (ra0.symm.trans rc0))
    (hL0 : L0.Homotopic (rl0.symm.trans ra0))
    (hR0 : R0.Homotopic (rr0.symm.trans rc0))
    (hU1 : U1.Homotopic (ra1.symm.trans rc1))
    (hL1 : L1.Homotopic (rl1.symm.trans ra1))
    (hR1 : R1.Homotopic (rr1.symm.trans rc1))
    (a : Path a1 a0) (β : Path r0 l1) (c : Path c1 c0) (d : Path l0 r1)
    (hold : q.whiskeredLoopClass
      (((((ra1.trans a).trans ra0.symm).trans ((rr0.trans β).trans rl1.symm)).trans
        ((rc1.trans c).trans rc0.symm)).trans ((rl0.trans d).trans rr1.symm)) ∉ J) :
    (q.trans ra1).whiskeredLoopClass (((a.trans U0).trans c.symm).trans U1.symm) ∉ J ∨
      (q.trans ra1).whiskeredLoopClass
        (((((((a.trans L0.symm).trans d).trans R1).trans c).trans R0.symm).trans
          β).trans L1) ∉ J := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hFirst, hSecond⟩ := resolution_end_words_case_b p q
    ra0 rc0 rl0 rr0 ra1 rc1 rl1 rr1 U0 L0 R0 U1 L1 R1
    hU0 hL0 hR0 hU1 hL1 hR1 a β c d
  have hOld := (resolution_words_case_b q p
    ((ra1.trans a).trans ra0.symm) ((rc1.trans c).trans rc0.symm)
    ((rr0.trans β).trans rl1.symm) ((rl0.trans d).trans rr1.symm)).1
  rw [← basedPathWord_radial, ← basedPathWord_radial,
    ← basedPathWord_radial, ← basedPathWord_radial] at hOld
  apply hold
  apply J.inv_mem_iff.mp
  change basedPathWord q q _ ∈ J
  rw [hOld]
  apply old_word_mem_of_case_b J
  · rw [← hFirst, basedPathWord_loop]
    exact J.inv_mem h.1
  · rw [← hSecond, basedPathWord_loop]
    exact J.inv_mem h.2

end PoincareConjecture.M76.Dehn
