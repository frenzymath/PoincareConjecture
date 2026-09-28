import PoincareConjecture.Proofs.M76.Dehn.Mathlib.WhiskeredLoopSplit
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OldWordNormalSubgroup











set_option autoImplicit false

namespace PoincareConjecture.M76.Dehn

variable {X : Type*} [TopologicalSpace X] {b x y z : X}



noncomputable def basedPathWord (p : Path b x) (q : Path b y) (a : Path x y) :
    FundamentalGroup X b :=
  (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((p.trans a).trans q.symm)))⁻¹


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


theorem basedPathWord_refl (p : Path b x) :
    basedPathWord p p (Path.refl x) = 1 := by
  change (p.whiskeredLoopClass (Path.refl x))⁻¹ = 1
  rw [Path.whiskeredLoopClass_refl, inv_one]


theorem basedPathWord_congr (p : Path b x) (q : Path b y)
    {a c : Path x y} (h : a.Homotopic c) :
    basedPathWord p q a = basedPathWord p q c := by
  unfold basedPathWord
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq.mpr h]


theorem basedPathWord_symm (p : Path b x) (q : Path b y) (a : Path x y) :
    basedPathWord q p a.symm = (basedPathWord p q a)⁻¹ := by
  have h : basedPathWord p q a * basedPathWord q p a.symm = 1 := by
    rw [← basedPathWord_trans]
    exact (basedPathWord_congr p p (Path.Homotopic.trans_symm a)).trans
      (basedPathWord_refl p)
  exact eq_inv_of_mul_eq_one_right h


theorem basedPathWord_loop (p : Path b x) (a : Path x x) :
    basedPathWord p p a = (p.whiskeredLoopClass a)⁻¹ := rfl


theorem basedPathWord_extend (p : Path b x) (a : Path x y) :
    basedPathWord p (p.trans a) a = 1 := by
  unfold basedPathWord
  change (FundamentalGroup.fromPath
    ((Path.Homotopic.Quotient.mk (p.trans a)).trans
      (Path.Homotopic.Quotient.mk (p.trans a)).symm))⁻¹ = 1
  rw [Path.Homotopic.Quotient.trans_symm]
  rfl



theorem basedPathWord_radial {x' y' : X}
    (p : Path b x) (q : Path b y) (r : Path x x') (s : Path y y') (a : Path x' y') :
    basedPathWord (p.trans r) (q.trans s) a =
      basedPathWord p q ((r.trans a).trans s.symm) := by
  rw [basedPathWord_trans p (q.trans s) q,
    basedPathWord_trans p (p.trans r) (q.trans s),
    basedPathWord_symm, basedPathWord_extend, basedPathWord_extend,
    inv_one, one_mul, mul_one]




theorem basedPathWord_end_path {x' y' : X}
    (p : Path b x) (r : Path x x') (s : Path x y') (a : Path x' y')
    (ha : a.Homotopic (r.symm.trans s)) :
    basedPathWord (p.trans r) (p.trans s) a = 1 := by
  rw [basedPathWord_congr _ _ ha, basedPathWord_trans (p.trans r) p (p.trans s),
    basedPathWord_symm, basedPathWord_extend, basedPathWord_extend, inv_one, one_mul]



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

end PoincareConjecture.M76.Dehn
