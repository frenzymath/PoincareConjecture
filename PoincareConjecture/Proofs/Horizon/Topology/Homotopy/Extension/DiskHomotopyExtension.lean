import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereDiskExtension

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace Poincare.Topology

noncomputable section

theorem exists_disk_prism_retraction
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ R : C(unitInterval × closedBall (0 : E) 1,
        {p : unitInterval × closedBall (0 : E) 1 // p.1 = 0 ∨ ‖p.2.val‖ = 1}),
      ∀ p : {p : unitInterval × closedBall (0 : E) 1 // p.1 = 0 ∨ ‖p.2.val‖ = 1},
        (R p.val).val = p.val := by
  let D := closedBall (0 : E) 1
  let A : Set (unitInterval × D) := {p | p.1 = 0 ∨ ‖p.2.val‖ = 1}
  let d (p : unitInterval × D) : ℝ := max (1 - (p.1 : ℝ) / 2) ‖p.2.val‖
  have hdcont : Continuous d := by fun_prop
  have hdle (p : unitInterval × D) : d p ≤ 1 := by
    apply max_le
    · linarith [p.1.property.1]
    · exact mem_closedBall_zero_iff.mp p.2.property
  have hdpos (p : unitInterval × D) : 0 < d p := by
    have h := le_max_left (1 - (p.1 : ℝ) / 2) ‖p.2.val‖
    change 1 - (p.1 : ℝ) / 2 ≤ d p at h
    linarith [p.1.property.2]
  have hdt (p : unitInterval × D) : 1 - (p.1 : ℝ) / 2 ≤ d p := le_max_left _ _
  have hdx (p : unitInterval × D) : ‖p.2.val‖ ≤ d p := le_max_right _ _
  let t (p : unitInterval × D) : ℝ := 2 + ((p.1 : ℝ) - 2) / d p
  have ht0 (p : unitInterval × D) : 0 ≤ t p := by
    have h : (2 - (p.1 : ℝ)) / d p ≤ 2 :=
      (div_le_iff₀ (hdpos p)).mpr (by linarith [hdt p])
    dsimp only [t]
    have he : ((p.1 : ℝ) - 2) / d p = -((2 - (p.1 : ℝ)) / d p) := by ring
    rw [he]
    linarith
  have htle (p : unitInterval × D) : t p ≤ p.1 := by
    have h : 2 - (p.1 : ℝ) ≤ (2 - (p.1 : ℝ)) / d p :=
      (le_div_iff₀ (hdpos p)).mpr (by nlinarith [hdle p, p.1.property.2])
    dsimp only [t]
    have he : ((p.1 : ℝ) - 2) / d p = -((2 - (p.1 : ℝ)) / d p) := by ring
    rw [he]
    linarith
  let x (p : unitInterval × D) : E := (d p)⁻¹ • p.2.val
  have hx (p : unitInterval × D) : x p ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff]
    dsimp only [x]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hdpos p), ← div_eq_inv_mul]
    exact (div_le_one (hdpos p)).mpr (hdx p)
  have hside (p : unitInterval × D) : t p = 0 ∨ ‖x p‖ = 1 := by
    by_cases h : ‖p.2.val‖ ≤ 1 - (p.1 : ℝ) / 2
    · left
      have he : d p = 1 - (p.1 : ℝ) / 2 := max_eq_left h
      have hne : 1 - (p.1 : ℝ) / 2 ≠ 0 := he ▸ (hdpos p).ne'
      dsimp only [t]
      have hdiv : ((p.1 : ℝ) - 2) / (1 - (p.1 : ℝ) / 2) = -2 :=
        (div_eq_iff hne).mpr (by ring)
      rw [he, hdiv]
      norm_num
    · right
      have he : d p = ‖p.2.val‖ := max_eq_right (le_of_not_ge h)
      have hne : ‖p.2.val‖ ≠ 0 := he ▸ (hdpos p).ne'
      simp [x, he, norm_smul, hne]
  let R : C(unitInterval × D, A) :=
    ⟨fun p => ⟨(⟨t p, ht0 p, (htle p).trans p.1.property.2⟩, ⟨x p, hx p⟩),
      (hside p).imp (fun h => Subtype.ext h) id⟩, by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact continuous_const.add
            (((continuous_subtype_val.comp continuous_fst).sub continuous_const).div hdcont
              (fun p => (hdpos p).ne'))
        · apply Continuous.subtype_mk
          exact (hdcont.inv₀ (fun p => (hdpos p).ne')).smul
            (continuous_subtype_val.comp continuous_snd)⟩
  refine ⟨R, fun p => ?_⟩
  have hd : d p.val = 1 := by
    apply le_antisymm (hdle p.val)
    rcases p.property with hp | hp
    · have ht : (p.val.1 : ℝ) = 0 := congrArg Subtype.val hp
      simpa only [ht, zero_div, sub_zero] using hdt p.val
    · simpa only [hp] using hdx p.val
  apply Prod.ext
  · apply Subtype.ext
    change t p.val = p.val.1
    dsimp only [t]
    rw [hd, div_one]
    ring
  · apply Subtype.ext
    change x p.val = p.val.2.val
    simp [x, hd]

theorem exists_disk_homotopy_extension
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Type v} [TopologicalSpace Y]
    (f : C(closedBall (0 : E) 1, Y))
    (H : C(unitInterval × sphere (0 : E) 1, Y))
    (h0 : ∀ z : sphere (0 : E) 1,
      H (0, z) = f ⟨z.val, sphere_subset_closedBall z.property⟩) :
    ∃ F : C(unitInterval × closedBall (0 : E) 1, Y),
      (∀ z, F (0, z) = f z) ∧
      (∀ (t : unitInterval) (z : sphere (0 : E) 1),
        F (t, ⟨z.val, sphere_subset_closedBall z.property⟩) = H (t, z)) := by
  let D := closedBall (0 : E) 1
  let S := sphere (0 : E) 1
  let A : Set (unitInterval × D) := {p | p.1 = 0 ∨ ‖p.2.val‖ = 1}
  let Q : C(D ⊕ (unitInterval × S), A) :=
    ⟨Sum.elim (fun z => ⟨(0, z), Or.inl rfl⟩)
      (fun p => ⟨(p.1, ⟨p.2.val, sphere_subset_closedBall p.2.property⟩),
        Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)⟩), by
          apply continuous_sum_dom.mpr
          constructor <;> fun_prop⟩
  have hsurj : Function.Surjective Q := by
    rintro ⟨p, hp⟩
    rcases hp with hp | hp
    · exact ⟨Sum.inl p.2, Subtype.ext (Prod.ext hp.symm rfl)⟩
    · exact ⟨Sum.inr (p.1, ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hp⟩), rfl⟩
  let g : C(D ⊕ (unitInterval × S), Y) :=
    ⟨Sum.elim f H, continuous_sum_dom.mpr ⟨f.continuous, H.continuous⟩⟩
  have hfactor : Function.FactorsThrough g Q := by
    intro a b hab
    cases a with
    | inl z =>
      cases b with
      | inl w => exact congrArg f (congrArg (fun p : A => p.val.2) hab)
      | inr p =>
        have ht : (0 : unitInterval) = p.1 := congrArg (fun p : A => p.val.1) hab
        have hz : z = ⟨p.2.val, sphere_subset_closedBall p.2.property⟩ :=
          congrArg (fun p : A => p.val.2) hab
        change f z = H p
        exact (congrArg f hz).trans ((h0 p.2).symm.trans (congrArg H (Prod.ext ht rfl)))
    | inr p =>
      cases b with
      | inl z =>
        have ht : p.1 = (0 : unitInterval) := congrArg (fun p : A => p.val.1) hab
        have hz : (⟨p.2.val, sphere_subset_closedBall p.2.property⟩ : D) = z :=
          congrArg (fun p : A => p.val.2) hab
        change H p = f z
        exact (congrArg H (show p = (0, p.2) from Prod.ext ht rfl)).trans
          ((h0 p.2).trans (congrArg f hz))
      | inr q =>
        have ht : p.1 = q.1 := congrArg (fun p : A => p.val.1) hab
        have hx : p.2.val = q.2.val := congrArg (fun p : A => p.val.2.val) hab
        exact congrArg H (Prod.ext ht (Subtype.ext hx))
  have hQ : _root_.Topology.IsQuotientMap Q :=
    .of_surjective_continuous hsurj Q.continuous
  let G := hQ.lift g hfactor
  have hG (z : D ⊕ (unitInterval × S)) : G (Q z) = g z :=
    DFunLike.congr_fun (hQ.lift_comp g hfactor) z
  obtain ⟨R, hR⟩ := exists_disk_prism_retraction E
  refine ⟨G.comp R, ?_, ?_⟩
  · intro z
    have he : R (0, z) = Q (Sum.inl z) := Subtype.ext (hR ⟨(0, z), Or.inl rfl⟩)
    change G (R (0, z)) = f z
    rw [he]
    exact hG (Sum.inl z)
  · intro t z
    have he : R (t, ⟨z.val, sphere_subset_closedBall z.property⟩) =
        Q (Sum.inr (t, z)) :=
      Subtype.ext (hR ⟨(t, ⟨z.val, sphere_subset_closedBall z.property⟩),
        Or.inr (mem_sphere_zero_iff_norm.mp z.property)⟩)
    change G (R (t, ⟨z.val, sphere_subset_closedBall z.property⟩)) = H (t, z)
    rw [he]
    exact hG (Sum.inr (t, z))

end

end Poincare.Topology
