import PoincareConjecture.Statement

set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.Proofs.M02

theorem exists_threeSphereCWComplex :
    ∃ C : Topology.CWComplex (Set.univ : Set PoincareConjecture.ThreeSphere),
      letI := C
      Topology.CWComplex.Finite (Set.univ : Set PoincareConjecture.ThreeSphere) ∧
        ∀ n : ℕ, n ≠ 0 → n ≠ 3 →
          IsEmpty (Topology.CWComplex.cell (Set.univ : Set PoincareConjecture.ThreeSphere) n) := by
  classical
  let P := Fin 3 → ℝ
  let U := ball (0 : P) 1
  let e : OnePoint U ≃ₜ ThreeSphere :=
    (Homeomorph.unitBall (E := P)).symm.onePointCongr.trans
      (onePointEquivSphereOfFinrankEq (V := P) (ι := Fin 4) (by simp [P]))
  let p : ThreeSphere := e OnePoint.infty
  let q : P → OnePoint U := fun x =>
    if hx : x ∈ U then OnePoint.some ⟨x, hx⟩ else OnePoint.infty
  have hq_some (x : U) : q x = OnePoint.some x := by simp [q, x.property]
  have hq_cont : Continuous q := by
    refine continuous_def.mpr fun s hs => ?_
    by_cases hinfty : OnePoint.infty ∈ s
    · have heq : q ⁻¹' s = (Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' s)ᶜ)ᶜ := by
        ext x
        change q x ∈ s ↔ x ∉ Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' s)ᶜ
        constructor
        · intro hx
          rintro ⟨z, hz, rfl⟩
          exact hz (by simpa only [mem_preimage, hq_some] using hx)
        · intro hx
          by_cases hxU : x ∈ U
          · by_contra hxs
            apply hx
            refine ⟨⟨x, hxU⟩, ?_, rfl⟩
            simpa only [mem_compl_iff, mem_preimage, ← hq_some] using hxs
          · simpa [q, hxU] using hinfty
      rw [heq]
      exact (((OnePoint.isOpen_def.mp hs).1 hinfty).image
        continuous_subtype_val).isClosed.isOpen_compl
    · have heq : q ⁻¹' s = Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' s) := by
        ext x
        constructor
        · intro hx
          by_cases hxU : x ∈ U
          · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
            simpa only [mem_preimage, ← hq_some] using hx
          · exact (hinfty (by simpa [q, hxU] using hx)).elim
        · rintro ⟨z, hz, rfl⟩
          simpa only [mem_preimage, hq_some] using hz
      rw [heq]
      exact isOpen_ball.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp hs).2
  let r : OnePoint U → P := OnePoint.rec 0 fun x => x.val
  have hpreimage (y : ThreeSphere) (hy : y ≠ p) :
      ∃ x : U, e.symm y = OnePoint.some x := by
    have hne : e.symm y ≠ OnePoint.infty := by
      intro h
      apply hy
      rw [← e.apply_symm_apply y, h]
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp hne
    exact ⟨x, hx.symm⟩
  let f3 : PartialEquiv P ThreeSphere := {
    toFun := e ∘ q
    invFun := r ∘ e.symm
    source := U
    target := {p}ᶜ
    map_source' := by
      intro x hx
      change e (q x) ≠ p
      intro h
      have he := e.injective h
      simp [q, hx] at he
    map_target' := by
      intro y hy
      obtain ⟨x, hx⟩ := hpreimage y hy
      change r (e.symm y) ∈ U
      rw [hx]
      exact x.property
    left_inv' := by
      intro x hx
      change r (e.symm (e (q x))) = x
      rw [e.symm_apply_apply]
      rw [hq_some ⟨x, hx⟩]
      rfl
    right_inv' := by
      intro y hy
      obtain ⟨x, hx⟩ := hpreimage y hy
      change e (q (r (e.symm y))) = y
      rw [hx]
      change e (q x.val) = y
      rw [hq_some, ← hx, e.apply_symm_apply] }
  have h3_image : f3 '' ball 0 1 = {p}ᶜ := f3.image_source_eq_target
  have h3_cont : ContinuousOn f3 (closedBall 0 1) :=
    (e.continuous.comp hq_cont).continuousOn
  have h3_symm : ContinuousOn f3.symm f3.target := by
    intro y hy
    obtain ⟨x, hx⟩ := hpreimage y hy
    have hr : ContinuousAt r (OnePoint.some x) :=
      OnePoint.continuousAt_coe.mpr continuous_subtype_val.continuousAt
    change ContinuousWithinAt (r ∘ e.symm) f3.target y
    exact ((hx ▸ hr).comp e.symm.continuous.continuousAt).continuousWithinAt
  let f0 : PartialEquiv (Fin 0 → ℝ) ThreeSphere := {
    toFun := fun _ => p
    invFun := fun _ => 0
    source := ball 0 1
    target := {p}
    map_source' := by intro x hx; rfl
    map_target' := by intro y hy; simp
    left_inv' := by intro x hx; exact Subsingleton.elim _ _
    right_inv' := by intro y hy; exact hy.symm }
  have h0_image : f0 '' ball 0 1 = {p} := f0.image_source_eq_target
  have h0_sphere : sphere (0 : Fin 0 → ℝ) 1 = ∅ := by
    exact sphere_eq_empty_of_subsingleton one_ne_zero
  let cell : ℕ → Type := fun n => PLift (n = 0 ∨ n = 3)
  let cmap : (n : ℕ) → cell n → PartialEquiv (Fin n → ℝ) ThreeSphere := by
    intro n i
    by_cases hn : n = 0
    · subst n
      exact f0
    · have hn3 : n = 3 := i.down.resolve_left hn
      subst n
      exact f3
  have cmap0 (i : cell 0) : cmap 0 i = f0 := by simp [cmap]
  have cmap3 (i : cell 3) : cmap 3 i = f3 := by simp [cmap]
  have hempty (n : ℕ) (hn0 : n ≠ 0) (hn3 : n ≠ 3) : IsEmpty (cell n) :=
    ⟨fun i => i.down.elim hn0 hn3⟩
  have hevent : ∀ᶠ n in Filter.atTop, IsEmpty (cell n) := by
    refine Filter.eventually_atTop.mpr ⟨4, ?_⟩
    intro n hn
    exact hempty n (by omega) (by omega)
  have hfinite (n : ℕ) : _root_.Finite (cell n) := inferInstance
  have hsource (n : ℕ) (i : cell n) : (cmap n i).source = ball 0 1 := by
    rcases i.down with hn | hn <;> subst n
    · rw [cmap0]
    · rw [cmap3]
  have hcont (n : ℕ) (i : cell n) : ContinuousOn (cmap n i) (closedBall 0 1) := by
    rcases i.down with hn | hn <;> subst n
    · rw [cmap0]
      exact continuousOn_const
    · rw [cmap3]
      exact h3_cont
  have hsymm (n : ℕ) (i : cell n) :
      ContinuousOn (cmap n i).symm (cmap n i).target := by
    rcases i.down with hn | hn <;> subst n
    · rw [cmap0]
      exact continuousOn_const
    · rw [cmap3]
      exact h3_symm
  have hdisjoint : (univ : Set (Σ n, cell n)).PairwiseDisjoint
      (fun ni => cmap ni.1 ni.2 '' ball 0 1) := by
    rintro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    have hnm : n ≠ m := by
      intro h
      subst m
      exact hne (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))
    rcases i.down with hn | hn <;> subst n
    · rcases j.down with hm | hm <;> subst m
      · exact (hne (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))).elim
      · change Disjoint (cmap 0 i '' ball 0 1) (cmap 3 j '' ball 0 1)
        rw [cmap0, cmap3, h0_image, h3_image]
        exact disjoint_compl_right
    · rcases j.down with hm | hm <;> subst m
      · change Disjoint (cmap 3 i '' ball 0 1) (cmap 0 j '' ball 0 1)
        rw [cmap3, cmap0, h3_image, h0_image]
        exact disjoint_compl_left
      · exact (hne (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))).elim
  have hmaps (n : ℕ) (i : cell n) : MapsTo (cmap n i) (sphere 0 1)
      (⋃ (m < n) (j : cell m), cmap m j '' closedBall 0 1) := by
    rcases i.down with hn | hn <;> subst n
    · intro x hx
      simp only [h0_sphere, mem_empty_iff_false] at hx
    · intro x hx
      have hxU : x ∉ U := by
        have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
        simp [U, hnorm]
      have hfp : cmap 3 i x = p := by simp [cmap3, f3, q, hxU, p]
      rw [hfp]
      refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by decide, mem_iUnion.mpr
        ⟨⟨Or.inl rfl⟩, 0, by simp, ?_⟩⟩⟩
      simp [cmap0, f0]
  have hunion : (⋃ (n : ℕ) (i : cell n), cmap n i '' closedBall 0 1) = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y = p
    · subst y
      refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨⟨Or.inl rfl⟩, 0, by simp, ?_⟩⟩
      simp [cmap0, f0]
    · have hymem : y ∈ f3 '' ball 0 1 := by
        rw [h3_image]
        exact hy
      obtain ⟨x, hx, rfl⟩ := hymem
      refine mem_iUnion.mpr ⟨3, mem_iUnion.mpr
        ⟨⟨Or.inr rfl⟩, x, ball_subset_closedBall hx, ?_⟩⟩
      rw [cmap3]
  let C := CWComplex.mkFinite univ cell cmap hevent hfinite hsource hcont hsymm
    hdisjoint hmaps hunion
  refine ⟨C, ?_, ?_⟩
  · exact CWComplex.finite_mkFinite univ cell cmap hevent hfinite hsource hcont hsymm
      hdisjoint hmaps hunion
  · intro n hn0 hn3
    exact hempty n hn0 hn3

end PoincareConjecture.Proofs.M02
