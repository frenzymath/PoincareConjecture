import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.WhiskeredLoopSplit
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.OldWordNormalSubgroup

/-!
# Based words of the two double-arc resolutions

Use the inverse of the whiskered path class to put multiplication in geometric
path order. The two endpoint whiskers cancel at every junction, giving the
literal nonabelian words in Dehn039, section 7, and Hatcher, printed p. 57.
The lemmas below do not identify a constructed disk's rim with these traversals;
that identification still uses the complete boundary attachment equations.
-/

set_option autoImplicit false

namespace PoincareMT.M76.Dehn

variable {X : Type*} [TopologicalSpace X] {b x y z : X}

/-- A path with an actual whisker to each endpoint, based at the original
mark. Inversion compensates for Mathlib's reversed multiplication order. -/
noncomputable def basedPathWord (p : Path b x) (q : Path b y) (a : Path x y) :
    FundamentalGroup X b :=
  (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((p.trans a).trans q.symm)))⁻¹

/-- The intermediate endpoint whisker cancels under concatenation. -/
theorem basedPathWord_trans (p : Path b x) (q : Path b y) (r : Path b z)
    (a : Path x y) (c : Path y z) :
    basedPathWord p r (a.trans c) = basedPathWord p q a * basedPathWord q r c := by
  apply inv_injective
  rw [mul_inv_rev]
  simp only [basedPathWord, inv_inv, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk q).symm (Path.Homotopic.Quotient.mk q),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- Constant paths contribute the identity with the same endpoint whisker. -/
theorem basedPathWord_refl (p : Path b x) :
    basedPathWord p p (Path.refl x) = 1 := by
  change (p.whiskeredLoopClass (Path.refl x))⁻¹ = 1
  rw [Path.whiskeredLoopClass_refl, inv_one]

/-- Endpoint-relative homotopies preserve the word and both actual whiskers. -/
theorem basedPathWord_congr (p : Path b x) (q : Path b y)
    {a c : Path x y} (h : a.Homotopic c) :
    basedPathWord p q a = basedPathWord p q c := by
  unfold basedPathWord
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq.mpr h]

/-- Reversing a path swaps its two whiskers and inverts its word. -/
theorem basedPathWord_symm (p : Path b x) (q : Path b y) (a : Path x y) :
    basedPathWord q p a.symm = (basedPathWord p q a)⁻¹ := by
  have h : basedPathWord p q a * basedPathWord q p a.symm = 1 := by
    rw [← basedPathWord_trans]
    exact (basedPathWord_congr p p (Path.Homotopic.trans_symm a)).trans
      (basedPathWord_refl p)
  exact eq_inv_of_mul_eq_one_right h

/-- At a loop, the word is the inverse of the ordinary whiskered class. -/
theorem basedPathWord_loop (p : Path b x) (a : Path x x) :
    basedPathWord p p a = (p.whiskeredLoopClass a)⁻¹ := rfl

/-- Extending the endpoint whisker along the actual path contributes no word. -/
theorem basedPathWord_extend (p : Path b x) (a : Path x y) :
    basedPathWord p (p.trans a) a = 1 := by
  unfold basedPathWord
  change (FundamentalGroup.fromPath
    ((Path.Homotopic.Quotient.mk (p.trans a)).trans
      (Path.Homotopic.Quotient.mk (p.trans a)).symm))⁻¹ = 1
  rw [Path.Homotopic.Quotient.trans_symm]
  rfl

/-- Radial end segments can be moved between the actual path and its endpoint
whiskers without changing the word. -/
theorem basedPathWord_radial {x' y' : X}
    (p : Path b x) (q : Path b y) (r : Path x x') (s : Path y y') (a : Path x' y') :
    basedPathWord (p.trans r) (q.trans s) a =
      basedPathWord p q ((r.trans a).trans s.symm) := by
  rw [basedPathWord_trans p (q.trans s) q,
    basedPathWord_trans p (p.trans r) (q.trans s),
    basedPathWord_symm, basedPathWord_extend, basedPathWord_extend,
    inv_one, one_mul, mul_one]

/-- A resolved end path has trivial based word when compared with the two
radial whiskers in its own endpoint square. Its complete endpoint-relative
homotopy, as constructed by `exists_resolution_end_path`, suffices. -/
theorem basedPathWord_end_path {x' y' : X}
    (p : Path b x) (r : Path x x') (s : Path x y') (a : Path x' y')
    (ha : a.Homotopic (r.symm.trans s)) :
    basedPathWord (p.trans r) (p.trans s) a = 1 := by
  rw [basedPathWord_congr _ _ ha, basedPathWord_trans (p.trans r) p (p.trans s),
    basedPathWord_symm, basedPathWord_extend, basedPathWord_extend, inv_one, one_mul]

/-- The actual four old portions and the two case-(a) traversals have the
three required words, for any retained pair of endpoint whiskers. -/
theorem resolution_words_case_a (p : Path b x) (q : Path b y)
    (a : Path x y) (c : Path y x) (d : Path x x) (β : Path y y) :
    let A := basedPathWord p q a
    let B := basedPathWord q q β
    let C := basedPathWord q p c
    let D := basedPathWord p p d
    basedPathWord p p (((a.trans β).trans c).trans d) = A * B * C * D ∧
      basedPathWord p p (a.trans c) = A * C ∧
      basedPathWord p p (((a.trans β.symm).trans c).trans d.symm) =
        A * B⁻¹ * C * D⁻¹ := by
  dsimp only
  simp only [basedPathWord_trans p p p, basedPathWord_trans p q p,
    basedPathWord_trans p q q, basedPathWord_symm, true_and]

/-- The alternating old portions and the two case-(b) traversals give the
other pair of nonabelian resolution words. -/
theorem resolution_words_case_b (p : Path b x) (q : Path b y)
    (a c : Path x y) (β d : Path y x) :
    let A := basedPathWord p q a
    let B := basedPathWord q p β
    let C := basedPathWord p q c
    let D := basedPathWord q p d
    basedPathWord p p (((a.trans β).trans c).trans d) = A * B * C * D ∧
      basedPathWord p p (a.trans c.symm) = A * C⁻¹ ∧
      basedPathWord p p (((a.trans d).trans c).trans β) = A * D * C * B := by
  dsimp only
  simp only [basedPathWord_trans p q p, basedPathWord_trans p p q,
    basedPathWord_symm, true_and]

/-- One case-(a) traversal remains outside the original normal subgroup,
with the original basepoint and ordinary (uninverted) whiskered class. -/
theorem resolution_excluded_case_a
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b x) (q : Path b y)
    (a : Path x y) (c : Path y x) (d : Path x x) (β : Path y y)
    (hold : p.whiskeredLoopClass (((a.trans β).trans c).trans d) ∉ J) :
    p.whiskeredLoopClass (a.trans c) ∉ J ∨
      p.whiskeredLoopClass (((a.trans β.symm).trans c).trans d.symm) ∉ J := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hOld, hFirst, hSecond⟩ := resolution_words_case_a p q a c d β
  apply hold
  apply J.inv_mem_iff.mp
  change basedPathWord p p (((a.trans β).trans c).trans d) ∈ J
  rw [hOld]
  apply old_word_mem_of_case_a J
  · rw [← hFirst, basedPathWord_loop]
    exact J.inv_mem h.1
  · rw [← hSecond, basedPathWord_loop]
    exact J.inv_mem h.2

/-- One case-(b) traversal remains outside that same normal subgroup. -/
theorem resolution_excluded_case_b
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b x) (q : Path b y)
    (a c : Path x y) (β d : Path y x)
    (hold : p.whiskeredLoopClass (((a.trans β).trans c).trans d) ∉ J) :
    p.whiskeredLoopClass (a.trans c.symm) ∉ J ∨
      p.whiskeredLoopClass (((a.trans d).trans c).trans β) ∉ J := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hOld, hFirst, hSecond⟩ := resolution_words_case_b p q a c β d
  apply hold
  apply J.inv_mem_iff.mp
  change basedPathWord p p (((a.trans β).trans c).trans d) ∈ J
  rw [hOld]
  apply old_word_mem_of_case_b J
  · rw [← hFirst, basedPathWord_loop]
    exact J.inv_mem h.1
  · rw [← hSecond, basedPathWord_loop]
    exact J.inv_mem h.2

end PoincareMT.M76.Dehn
