import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerArcStrips













noncomputable section
set_option autoImplicit false

open Set
open scoped Topology
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture





theorem m64Intrinsic_two_arc_interior_disjoint
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ}
    (hai : InjOn alpha (Icc 0 A))
    (hinter : (alpha '' Icc 0 A) ∩ (beta '' Icc 0 B) ⊆ {alpha 0, alpha A}) :
    Disjoint (alpha '' Ioo 0 A) (beta '' Icc 0 B) := by
  apply disjoint_left.mpr
  rintro p ⟨t, ht, rfl⟩ hp
  have hpoint := hinter ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hp⟩
  rcases (show alpha t = alpha 0 ∨ alpha t = alpha A by simpa using hpoint) with h0 | hA
  · have he := hai ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, (ht.1.trans ht.2).le⟩ h0
    exact ht.1.ne' he
  · have he := hai ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans ht.2).le, le_rfl⟩ hA
    exact ht.2.ne he





theorem m64Intrinsic_exists_two_arc_strip_width
    {ι κ : Type*} [Finite ι] [Finite κ]
    (F : ι → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (G : κ → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hFs : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ (F i).source)
    (hGs : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ (G j).source)
    {alpha beta : ℝ → AnnulusCoordinates} {a b c d rho sigma : ℝ}
    (hdisj : Disjoint (alpha '' Icc a b) (beta '' Icc c d))
    (hFa : ∀ i, (fun t => F i (t, 0)) '' Icc (0 : ℝ) 1 ⊆ alpha '' Icc a b)
    (hGa : ∀ j, (fun t => G j (t, 0)) '' Icc (0 : ℝ) 1 ⊆ beta '' Icc c d)
    (hrho : 0 < rho) (hsigma : 0 < sigma) :
    ∃ delta > 0, delta ≤ rho ∧ delta ≤ sigma ∧
      (∀ i, Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ (F i).source) ∧
      (∀ j, Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ (G j).source) ∧
      ∀ i j, Disjoint (F i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))
        (G j '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta)) := by
  classical
  let S : ι ⊕ κ → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates := Sum.elim F G
  let separate : ι ⊕ κ → ι ⊕ κ → Prop
    | .inl _, .inr _ => True
    | _, _ => False
  have hsource : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ (S i).source := by
    rintro (i | j)
    · exact hFs i
    · exact hGs j
  have hbase : ∀ i j, separate i j →
      Disjoint ((fun t => S i (t, 0)) '' Icc (0 : ℝ) 1)
        ((fun t => S j (t, 0)) '' Icc (0 : ℝ) 1) := by
    rintro (i | i) (j | j) h
    · exact h.elim
    · exact hdisj.mono (hFa i) (hGa j)
    · exact h.elim
    · exact h.elim
  obtain ⟨delta, hdelta, _, hsource', hseparate⟩ :=
    exists_finite_disjoint_strip_width S hsource separate hbase
      (fun _ => min rho sigma) (fun _ => lt_min hrho hsigma)
  let epsilon := min delta (min rho sigma)
  have hepsilon : 0 < epsilon := lt_min hdelta (lt_min hrho hsigma)
  have hsub : Icc (0 : ℝ) 1 ×ˢ Ioo (-epsilon) epsilon ⊆
      Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _))
  refine ⟨epsilon, hepsilon, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _),
    fun i => hsub.trans (hsource' (.inl i)),
    fun j => hsub.trans (hsource' (.inr j)), ?_⟩
  exact fun i j => (hseparate (.inl i) (.inr j) trivial).mono
    (image_mono hsub) (image_mono hsub)

end PoincareConjecture
