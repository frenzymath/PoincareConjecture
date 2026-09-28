import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ClosedIntervalProjection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]



theorem finitePL_interval_projection_image
    {φ : ℝ → F} {t : Set F} {a b : F}
    (hφ : FinitePiecewiseAffineOn φ (Icc (0 : ℝ) 1))
    (ht : IsFinitePLBallPair ℝ t {a, b})
    (hopen : φ '' Ioo (0 : ℝ) 1 ⊆ t)
    (hi : InjOn φ (Ioo (0 : ℝ) 1))
    (h0 : φ 0 ∈ ({a, b} : Set F)) (h1 : φ 1 ∈ ({a, b} : Set F)) :
    InjOn φ (Icc (0 : ℝ) 1) ∧ φ 0 ≠ φ 1 ∧ φ '' Icc (0 : ℝ) 1 = t := by
  have hmap : MapsTo φ (Icc (0 : ℝ) 1) t := by
    intro x hx
    by_cases hx0 : x = 0
    · exact hx0 ▸ ht.1 h0
    by_cases hx1 : x = 1
    · exact hx1 ▸ ht.1 h1
    exact hopen ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),
      lt_of_le_of_ne hx.2 hx1⟩, rfl⟩
  have htcopy := ht
  obtain ⟨_, c, _, _, _, e, ⟨k, hk, hke⟩, _⟩ := htcopy
  have hki : InjOn k t := by
    intro x hx y hy hxy
    apply congrArg Subtype.val (e.injective (show e ⟨x, hx⟩ = e ⟨y, hy⟩ from ?_))
    apply Subtype.ext
    simpa only [hke] using hxy
  have hci : InjOn (k ∘ φ) (Icc (0 : ℝ) 1) := by
    apply injOn_Icc_of_injOn_Ioo zero_lt_one
      (hk.continuousOn.comp hφ.continuousOn hmap)
    intro x hx y hy hxy
    exact hi hx hy (hki (hmap (Ioo_subset_Icc_self hx))
      (hmap (Ioo_subset_Icc_self hy)) hxy)
  have hclosed : InjOn φ (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact hci hx hy (congrArg k hxy)
  have hne : φ 0 ≠ φ 1 := by
    intro heq
    exact zero_ne_one (hclosed ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ heq)
  have hends : ({φ 0, φ 1} : Set F) = {a, b} := by
    simp only [mem_insert_iff, mem_singleton_iff] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact False.elim (hne (h0.trans h1.symm))
    · rw [h0, h1]
    · rw [h0, h1, pair_comm]
    · exact False.elim (hne (h0.trans h1.symm))
  have himage : IsFinitePLBallPair ℝ (φ '' Icc (0 : ℝ) 1) {φ 0, φ 1} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc zero_lt_one).image hφ hclosed
  refine ⟨hclosed, hne, himage.eq_of_subset_with_same_endpoints ?_ hmap.image_subset hne⟩
  simpa only [hends] using ht



theorem exists_finitePL_gap_projection_homeomorph
    {g : ℝ → E} {f : E → F} {t : Set F} {a b : F}
    (hg : FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1))
    (hgi : InjOn g (Icc (0 : ℝ) 1))
    (hf : FinitePiecewiseAffineOn f (g '' Icc (0 : ℝ) 1))
    (ht : IsFinitePLBallPair ℝ t {a, b})
    (hopen : f '' (g '' Ioo (0 : ℝ) 1) ⊆ t)
    (hfi : InjOn f (g '' Ioo (0 : ℝ) 1))
    (h0 : f (g 0) ∈ ({a, b} : Set F)) (h1 : f (g 1) ∈ ({a, b} : Set F)) :
    ∃ e : (g '' Icc (0 : ℝ) 1) ≃ₜ t,
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧ ∀ x, (e x : F) = f x := by
  have hcomp : FinitePiecewiseAffineOn (f ∘ g) (Icc (0 : ℝ) 1) :=
    hf.comp hg (fun x hx ↦ ⟨x, hx, rfl⟩)
  have hcompOpen : (f ∘ g) '' Ioo (0 : ℝ) 1 ⊆ t := by
    simpa only [image_comp] using hopen
  have hcompI : InjOn (f ∘ g) (Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact hgi (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
      (hfi ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy)
  obtain ⟨hclosed, _, himage⟩ :=
    finitePL_interval_projection_image hcomp ht hcompOpen hcompI h0 h1
  have hfinj : InjOn f (g '' Icc (0 : ℝ) 1) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact congrArg g (hclosed hx hy hxy)
  have htarget : f '' (g '' Icc (0 : ℝ) 1) = t := by
    simpa only [image_comp] using himage
  obtain ⟨e, _, heval⟩ := hf.exists_homeomorph_image hfinj
  let et := e.trans (Homeomorph.setCongr htarget)
  have het : et.IsFinitePL := ⟨f, hf, heval⟩
  exact ⟨et, het, het.symm, heval⟩

end PoincareConjecture.M76.OriginalTriangleCopies
