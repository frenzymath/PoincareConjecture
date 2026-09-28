import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

theorem exists_iUnion_finitePL {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    (S : ι → Set E) (T : ι → Set F) (e : ∀ i, S i ≃ₜ T i)
    (he : ∀ i, (e i).IsFinitePL)
    (hoverlap : ∀ i j (x : S i), (x : E) ∈ S j ↔ (e i x : F) ∈ T j)
    (hagree : ∀ i j (x : E) (hi : x ∈ S i) (hj : x ∈ S j),
      (e i ⟨x, hi⟩ : F) = e j ⟨x, hj⟩) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      ∀ i (x : S i), (H ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : F) = e i x := by
  classical
  let f : E → F := fun x => if hx : x ∈ ⋃ i, S i then
    e (mem_iUnion.mp hx).choose ⟨x, (mem_iUnion.mp hx).choose_spec⟩ else 0
  have hfval (i : ι) (x : S i) : f x = (e i x : F) := by
    have hx : (x : E) ∈ ⋃ i, S i := mem_iUnion.mpr ⟨i, x.property⟩
    dsimp only [f]
    rw [dif_pos hx]
    exact hagree _ i x _ x.property
  have hfPL (i : ι) : FinitePiecewiseAffineOn f (S i) := by
    obtain ⟨g, hg, hge⟩ := he i
    exact hg.congr fun x hx => (hge ⟨x, hx⟩).symm.trans (hfval i ⟨x, hx⟩).symm
  have hinj : InjOn f (⋃ i, S i) := by
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hxy' : (e i ⟨x, hxi⟩ : F) = e j ⟨y, hyj⟩ := by
      rw [← hfval, ← hfval]
      exact hxy
    have hxj : x ∈ S j := (hoverlap i j ⟨x, hxi⟩).mpr (hxy'.symm ▸ (e j ⟨y, hyj⟩).property)
    have heq : e j ⟨x, hxj⟩ = e j ⟨y, hyj⟩ :=
      Subtype.ext ((hagree i j x hxi hxj).symm.trans hxy')
    exact congrArg Subtype.val ((e j).injective heq)
  have himage : f '' (⋃ i, S i) = ⋃ i, T i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [hfval i ⟨x, hxi⟩]
      exact mem_iUnion.mpr ⟨i, (e i ⟨x, hxi⟩).property⟩
    · intro hy
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
      let x := (e i).symm ⟨y, hyi⟩
      refine ⟨x, mem_iUnion.mpr ⟨i, x.property⟩, ?_⟩
      rw [hfval]
      exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hyi⟩)
  have hex := (FinitePiecewiseAffineOn.iUnion hfPL).exists_homeomorph_image hinj
  rw [himage] at hex
  obtain ⟨H, hH, hHval⟩ := hex
  exact ⟨H, hH, fun i x => (hHval _).trans (hfval i x)⟩

end Homeomorph
