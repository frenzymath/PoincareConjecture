import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.ResolutionEndWordCalculation

/-!
# Cyclic rotation of the actual resolution paths

The terminal attachment is based at its C endpoint, whereas the end-word
calculation starts at A. Cyclic rotation conjugates the based word with the
actual endpoint whiskers and preserves membership in the original normal
subgroup. See Dehn039, sections 6--7, and Hatcher, section 3.1, printed pp. 56--57.
-/

set_option autoImplicit false

namespace PoincareMT.M76.Dehn

variable {X : Type*} [TopologicalSpace X] {b x y : X}

/-- Rotating two actual path portions conjugates their word; the two
endpoint whiskers are arbitrary retained paths from the original basepoint. -/
theorem basedPathWord_cycle (p : Path b x) (q : Path b y)
    (a : Path x y) (c : Path y x) :
    basedPathWord q q (c.trans a) =
      (basedPathWord p q a)⁻¹ * basedPathWord p p (a.trans c) * basedPathWord p q a := by
  rw [basedPathWord_trans q p q, basedPathWord_trans p q p]
  group

/-- Normal-subgroup membership is unchanged by cyclic rotation, including
the change between the two actual endpoint whiskers. -/
theorem basedPathWord_cycle_mem_iff
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b x) (q : Path b y) (a : Path x y) (c : Path y x) :
    basedPathWord q q (c.trans a) ∈ J ↔ basedPathWord p p (a.trans c) ∈ J := by
  rw [basedPathWord_trans q p q, basedPathWord_trans p q p]
  exact Subgroup.Normal.mem_comm_iff ‹J.Normal›

end PoincareMT.M76.Dehn

namespace Path

open PoincareMT.M76.Dehn

variable {X : Type*} [TopologicalSpace X] {b x y : X}

/-- Endpoint-relative homotopies retain the ordinary whiskered loop class. -/
theorem whiskeredLoopClass_congr (p : Path b x) {a c : Path x x}
    (h : a.Homotopic c) : p.whiskeredLoopClass a = p.whiskeredLoopClass c := by
  exact inv_injective (basedPathWord_congr p p h)

/-- The ordinary, uninverted whiskered class has the same explicit
conjugation formula under rotation of two path portions. -/
theorem whiskeredLoopClass_cycle (p : Path b x) (q : Path b y)
    (a : Path x y) (c : Path y x) :
    q.whiskeredLoopClass (c.trans a) =
      (basedPathWord p q a)⁻¹ * p.whiskeredLoopClass (a.trans c) * basedPathWord p q a := by
  have h := congrArg Inv.inv (basedPathWord_cycle p q a c)
  simpa only [basedPathWord_loop, inv_inv, mul_inv_rev, mul_assoc] using h

/-- Cyclically rotated loops have equivalent membership in a normal
subgroup, with no compatibility requirement on their actual whiskers. -/
theorem whiskeredLoopClass_cycle_mem_iff
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b x) (q : Path b y) (a : Path x y) (c : Path y x) :
    q.whiskeredLoopClass (c.trans a) ∈ J ↔ p.whiskeredLoopClass (a.trans c) ∈ J := by
  simpa only [basedPathWord_loop, J.inv_mem_iff] using basedPathWord_cycle_mem_iff J p q a c

/-- The rotation transfer also applies to the actual endpoint-relative
homotopic representatives returned by a source-rim construction. -/
theorem whiskeredLoopClass_cycle_mem_iff_of_homotopic
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b x) (q : Path b y) (a : Path x y) (c : Path y x)
    {old : Path x x} {rotated : Path y y}
    (hold : old.Homotopic (a.trans c)) (hrotated : rotated.Homotopic (c.trans a)) :
    q.whiskeredLoopClass rotated ∈ J ↔ p.whiskeredLoopClass old ∈ J := by
  rw [whiskeredLoopClass_congr q hrotated, whiskeredLoopClass_congr p hold]
  exact whiskeredLoopClass_cycle_mem_iff J p q a c

/-- An excluded actual rim remains excluded after rotation and replacement
by an endpoint-relative homotopic rim, with the new actual endpoint whisker. -/
theorem whiskeredLoopClass_cycle_excluded_of_homotopic
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b x) (q : Path b y) (a : Path x y) (c : Path y x)
    {old : Path x x} {rotated : Path y y}
    (hold : old.Homotopic (a.trans c)) (hrotated : rotated.Homotopic (c.trans a))
    (hout : p.whiskeredLoopClass old ∉ J) : q.whiskeredLoopClass rotated ∉ J :=
  fun h ↦ hout ((whiskeredLoopClass_cycle_mem_iff_of_homotopic J p q a c
    hold hrotated).mp h)

end Path

namespace PoincareMT.M76.Dehn

variable {X : Type*} [TopologicalSpace X] {b x y : X}

/-- The literal two rotated candidates inherit exclusion without any
homotopy input, even for independently chosen A and C whiskers. -/
theorem resolution_cycle_excluded_exact
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (pA : Path b x) (pC : Path b y)
    (a₀ a₁ : Path x y) (c₀ c₁ : Path y x)
    (hout : pA.whiskeredLoopClass (a₀.trans c₀) ∉ J ∨
      pA.whiskeredLoopClass (a₁.trans c₁) ∉ J) :
    pC.whiskeredLoopClass (c₀.trans a₀) ∉ J ∨
      pC.whiskeredLoopClass (c₁.trans a₁) ∉ J :=
  hout.imp (fun h hm ↦ h ((Path.whiskeredLoopClass_cycle_mem_iff J pA pC a₀ c₀).mp hm))
    (fun h hm ↦ h ((Path.whiskeredLoopClass_cycle_mem_iff J pA pC a₁ c₁).mp hm))

/-- Transfer the excluded-candidate disjunction to the two cyclically
rotated actual rims. Both candidates keep their chosen endpoint whisker. -/
theorem resolution_cycle_excluded
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (pA : Path b x) (pC : Path b y)
    (a₀ a₁ : Path x y) (c₀ c₁ : Path y x)
    {old₀ old₁ : Path x x} {new₀ new₁ : Path y y}
    (hOld₀ : old₀.Homotopic (a₀.trans c₀)) (hOld₁ : old₁.Homotopic (a₁.trans c₁))
    (hNew₀ : new₀.Homotopic (c₀.trans a₀)) (hNew₁ : new₁.Homotopic (c₁.trans a₁))
    (hout : pA.whiskeredLoopClass old₀ ∉ J ∨ pA.whiskeredLoopClass old₁ ∉ J) :
    pC.whiskeredLoopClass new₀ ∉ J ∨ pC.whiskeredLoopClass new₁ ∉ J :=
  hout.imp (Path.whiskeredLoopClass_cycle_excluded_of_homotopic J pA pC a₀ c₀ hOld₀ hNew₀)
    (Path.whiskeredLoopClass_cycle_excluded_of_homotopic J pA pC a₁ c₁ hOld₁ hNew₁)

variable {z0 z1 a0 a1 c0 c1 l0 l1 r0 r1 : X}

/-- Starting the case-(a) full traversals at C0 gives `A C` and
`D⁻¹ A B⁻¹ C`, with the literal C0 radial whisker. -/
theorem rotated_resolution_end_words_case_a
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
    basedPathWord (p.trans rc0) (p.trans rc0)
        (((U0.symm.trans a).trans U1).trans c) = A * C ∧
      basedPathWord (p.trans rc0) (p.trans rc0)
        (((((((R0.symm.trans d.symm).trans L0).trans a).trans L1.symm).trans
          β.symm).trans R1).trans c) = D⁻¹ * A * B⁻¹ * C := by
  dsimp only
  have hu0 := basedPathWord_end_path p ra0 rc0 U0 hU0
  have hl0 := basedPathWord_end_path p rl0 ra0 L0 hL0
  have hr0 := basedPathWord_end_path p rr0 rc0 R0 hR0
  have hu1 := basedPathWord_end_path q ra1 rc1 U1 hU1
  have hl1 := basedPathWord_end_path q rl1 ra1 L1 hL1
  have hr1 := basedPathWord_end_path q rr1 rc1 R1 hR1
  constructor
  · rw [basedPathWord_trans (p.trans rc0) (q.trans rc1) (p.trans rc0),
      basedPathWord_trans (p.trans rc0) (q.trans ra1) (q.trans rc1),
      basedPathWord_trans (p.trans rc0) (p.trans ra0) (q.trans ra1),
      basedPathWord_symm, hu0, hu1, inv_one, one_mul, mul_one]
  · rw [basedPathWord_trans (p.trans rc0) (q.trans rc1) (p.trans rc0),
      basedPathWord_trans (p.trans rc0) (q.trans rr1) (q.trans rc1),
      basedPathWord_trans (p.trans rc0) (q.trans rl1) (q.trans rr1),
      basedPathWord_trans (p.trans rc0) (q.trans ra1) (q.trans rl1),
      basedPathWord_trans (p.trans rc0) (p.trans ra0) (q.trans ra1),
      basedPathWord_trans (p.trans rc0) (p.trans rl0) (p.trans ra0),
      basedPathWord_trans (p.trans rc0) (p.trans rr0) (p.trans rl0)]
    simp only [basedPathWord_symm, hl0, hr0, hl1, hr1, inv_one, one_mul, mul_one]

/-- Rotating the case-(b) full traversals to C0 gives `C⁻¹ A` and
`B A D C`, retaining the same geometric orientations and actual whisker. -/
theorem rotated_resolution_end_words_case_b
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
    basedPathWord (p.trans rc0) (p.trans rc0)
        (((c.symm.trans U1.symm).trans a).trans U0) = C⁻¹ * A ∧
      basedPathWord (p.trans rc0) (p.trans rc0)
        (((((((R0.symm.trans β).trans L1).trans a).trans L0.symm).trans
          d).trans R1).trans c) = B * A * D * C := by
  dsimp only
  have hu0 := basedPathWord_end_path p ra0 rc0 U0 hU0
  have hl0 := basedPathWord_end_path p rl0 ra0 L0 hL0
  have hr0 := basedPathWord_end_path p rr0 rc0 R0 hR0
  have hu1 := basedPathWord_end_path q ra1 rc1 U1 hU1
  have hl1 := basedPathWord_end_path q rl1 ra1 L1 hL1
  have hr1 := basedPathWord_end_path q rr1 rc1 R1 hR1
  constructor
  · rw [basedPathWord_trans (p.trans rc0) (p.trans ra0) (p.trans rc0),
      basedPathWord_trans (p.trans rc0) (q.trans ra1) (p.trans ra0),
      basedPathWord_trans (p.trans rc0) (q.trans rc1) (q.trans ra1)]
    simp only [basedPathWord_symm, hu0, hu1, inv_one, mul_one]
  · rw [basedPathWord_trans (p.trans rc0) (q.trans rc1) (p.trans rc0),
      basedPathWord_trans (p.trans rc0) (q.trans rr1) (q.trans rc1),
      basedPathWord_trans (p.trans rc0) (p.trans rl0) (q.trans rr1),
      basedPathWord_trans (p.trans rc0) (p.trans ra0) (p.trans rl0),
      basedPathWord_trans (p.trans rc0) (q.trans ra1) (p.trans ra0),
      basedPathWord_trans (p.trans rc0) (q.trans rl1) (q.trans ra1),
      basedPathWord_trans (p.trans rc0) (p.trans rr0) (q.trans rl1)]
    simp only [basedPathWord_symm, hl0, hr0, hl1, hr1, inv_one, one_mul, mul_one]

end PoincareMT.M76.Dehn
