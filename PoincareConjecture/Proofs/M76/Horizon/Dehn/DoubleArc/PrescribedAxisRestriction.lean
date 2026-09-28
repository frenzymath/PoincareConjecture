import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_prescribed_axis_restriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A Z : Set E} {v m : E}
    (b : Icc (0 : ℝ) 1 ≃ₜ A) (hb : b.IsFinitePL)
    (hZ : IsFinitePLBallPair ℝ Z {v, m}) (hZA : Z ⊆ A) (hvm : v ≠ m) :
    ∃ (α β : Icc (0 : ℝ) 1) (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1)
      (axis : Icc (α : ℝ) (β : ℝ) ≃ₜ Z),
      α < β ∧ ({(b α : E), (b β : E)} : Set E) = {v, m} ∧
      axis.IsFinitePL ∧ ∀ t, (axis t : E) = (b ⟨t, hsub t.property⟩ : E) := by
  classical
  let tv := b.symm ⟨v, hZA (hZ.1 (Or.inl rfl))⟩
  let tm := b.symm ⟨m, hZA (hZ.1 (Or.inr rfl))⟩
  have htv : (b tv : E) = v := congrArg Subtype.val (b.apply_symm_apply _)
  have htm : (b tm : E) = m := congrArg Subtype.val (b.apply_symm_apply _)
  have htne : tv ≠ tm := fun heq => hvm (htv.symm.trans ((congrArg (fun t => (b t : E)) heq).trans htm))
  let α := min tv tm
  let β := max tv tm
  have hlt : α < β := min_lt_max.mpr htne
  have hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1 :=
    fun _ ht => ⟨α.property.1.trans ht.1, ht.2.trans β.property.2⟩
  have hends : ({(b α : E), (b β : E)} : Set E) = {v, m} := by
    rcases le_total tv tm with h | h
    · simp only [α, β, min_eq_left h, max_eq_right h, htv, htm]
    · simp only [α, β, min_eq_right h, max_eq_left h, htv, htm, pair_comm]
  obtain ⟨f, hf, hval⟩ := hb
  have hinj : InjOn f (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (b.injective
      (Subtype.ext ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have himage : f '' Icc (0 : ℝ) 1 = A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hval ⟨x, hx⟩]
      exact (b ⟨x, hx⟩).property
    · intro hy
      refine ⟨b.symm ⟨y, hy⟩, (b.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hval, b.apply_symm_apply]
  have hZ' : IsFinitePLBallPair ℝ Z {f α, f β} := by
    rw [← hval α, ← hval β, hends]
    exact hZ
  have hZimage : Z = f '' Icc (α : ℝ) (β : ℝ) :=
    hZ'.eq_image_Icc_of_subset hf hinj hlt hsub (hZA.trans himage.symm.subset)
  have hinterval := isFinitePLBallPair_Icc (show (α : ℝ) < (β : ℝ) from hlt)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hinterval
  have hfsub : FinitePiecewiseAffineOn f (Icc (α : ℝ) (β : ℝ)) := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hsub)
  obtain ⟨axis, haxis, haxisval⟩ := hfsub.exists_homeomorph_image (hinj.mono hsub)
  let axis' := axis.trans (Homeomorph.setCongr hZimage.symm)
  have haxis' : axis'.IsFinitePL := ⟨f, hfsub, haxisval⟩
  exact ⟨α, β, hsub, axis', hlt, hends, haxis',
    fun t => (haxisval t).trans (hval ⟨t, hsub t.property⟩).symm⟩

end PoincareConjecture.M76.Dehn
