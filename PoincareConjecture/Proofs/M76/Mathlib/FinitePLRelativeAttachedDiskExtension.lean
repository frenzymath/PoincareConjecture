import PoincareConjecture.Proofs.M76.Mathlib.FinitePLAttachedDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLAttachedDiskBoundaryCorrection










set_option autoImplicit false

open Set Geometry

namespace Set

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]






theorem IsFinitePLBallPair.exists_extension_of_attached_disk_and_boundary
    {s q d u w : Set X} {t r D U W : Set Y} {a b : X} {A B : Y}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (ht : IsFinitePLBallPair (ℝ × ℝ) t r)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (u ∪ w)) (hds : d ⊆ s)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (U ∪ W)) (hDt : D ⊆ t)
    (hu : IsFinitePLBallPair ℝ u {a, b}) (huq : u ⊆ q)
    (hw : IsFinitePLBallPair ℝ w {a, b}) (hab : a ≠ b)
    (hproper : w \ {a, b} ⊆ s \ q)
    (hU : IsFinitePLBallPair ℝ U {A, B}) (hUr : U ⊆ r)
    (hW : IsFinitePLBallPair ℝ W {A, B}) (hAB : A ≠ B)
    (hProper : W \ {A, B} ⊆ t \ r)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hmemu : ∀ x : d, (x : X) ∈ u ↔ (e x : Y) ∈ U)
    (hmemw : ∀ x : d, (x : X) ∈ w ↔ (e x : Y) ∈ W)
    (bnd : q ≃ₜ r) (hbnd : bnd.IsFinitePL)
    (hagree : ∀ x : u, (bnd ⟨x, huq x.property⟩ : Y) =
      (e ⟨x, hd.1 (Or.inl x.property)⟩ : Y)) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : d, H ⟨x, hds x.property⟩ = ⟨e x, hDt (e x).property⟩) ∧
      (∀ x : q, H ⟨x, hs.1 x.property⟩ = ⟨bnd x, ht.1 (bnd x).property⟩) ∧
      (∀ x : s, (x : X) ∈ d ↔ (H x : Y) ∈ D) ∧
      ∀ x : s, (x : X) ∈ q ↔ (H x : Y) ∈ r := by
  obtain ⟨E, hE, hEd, _, _, hEq⟩ := hs.exists_extension_of_attached_disk ht
    hd hds hD hDt hu huq hw hab hproper hU hUr hW hAB hProper e he hmemu hmemw
  let eq := E.restrictSubsets hs.1 ht.1 hEq
  have hbndcopy := hbnd
  obtain ⟨_, ⟨K, hK, hKq, _⟩, _⟩ := hbndcopy
  have heq : eq.IsFinitePL := hE.restrictSubsets hs.1 ht.1 hEq K hK hKq
  let g := eq.symm.trans bnd
  have hg : g.IsFinitePL := heq.symm.trans hbnd
  have hfix (y : r) (hy : (y : Y) ∈ U) : g y = y := by
    have hyD : (y : Y) ∈ D := hD.1 (Or.inl hy)
    let x := e.symm ⟨y, hyD⟩
    have hexy : e x = ⟨y, hyD⟩ := e.apply_symm_apply ⟨y, hyD⟩
    have hxu : (x : X) ∈ u := (hmemu x).mpr (by rwa [hexy])
    let z : q := ⟨x, huq hxu⟩
    have heqz : eq z = y := by
      apply Subtype.ext
      exact (congrArg (fun p : t => (p : Y)) (hEd x)).trans
        (congrArg (fun p : D => (p : Y)) hexy)
    have hbndz : bnd z = y := by
      apply Subtype.ext
      exact (hagree ⟨x, hxu⟩).trans (congrArg (fun p : D => (p : Y)) hexy)
    change bnd (eq.symm y) = y
    rw [← heqz, eq.symm_apply_apply]
    exact hbndz.trans heqz.symm
  obtain ⟨G, hG, hGD, hGr, _⟩ := ht.exists_boundary_extension_fix_attached_disk
    hD hDt hU hUr hW hAB hProper g hg hfix
  let H := E.trans G
  have hkeepd (x : d) : H ⟨x, hds x.property⟩ =
      ⟨e x, hDt (e x).property⟩ := by
    change G (E ⟨x, hds x.property⟩) = _
    rw [hEd x]
    exact hGD _ (e x).property
  have hkeepq (x : q) : H ⟨x, hs.1 x.property⟩ =
      ⟨bnd x, ht.1 (bnd x).property⟩ := by
    have hEx : E ⟨x, hs.1 x.property⟩ =
        ⟨eq x, ht.1 (eq x).property⟩ := rfl
    change G (E ⟨x, hs.1 x.property⟩) = _
    rw [hEx, hGr]
    apply Subtype.ext
    change (bnd (eq.symm (eq x)) : Y) = (bnd x : Y)
    rw [eq.symm_apply_apply]
  exact ⟨H, hE.trans hG, hkeepd, hkeepq,
    H.mem_subset_iff_of_extension e hds hDt hkeepd,
    H.mem_subset_iff_of_extension bnd hs.1 ht.1 hkeepq⟩

end Set
