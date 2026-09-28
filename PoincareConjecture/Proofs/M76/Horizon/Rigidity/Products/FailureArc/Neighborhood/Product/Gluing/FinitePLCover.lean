import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Geometry

namespace Geometry

theorem FinitePiecewiseAffineOn.of_parametrized_iUnion
    {ι : Type*} [Finite ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : ∀ i, E i → F) (s : ∀ i, Set (E i)) (f : F → G)
    (hq : ∀ i, FinitePiecewiseAffineOn (q i) (s i))
    (hi : ∀ i, InjOn (q i) (s i))
    (hf : ∀ i, FinitePiecewiseAffineOn (f ∘ q i) (s i)) :
    FinitePiecewiseAffineOn f (⋃ i, q i '' s i) := by
  classical
  apply FinitePiecewiseAffineOn.iUnion
  intro i
  have hinv := (hq i).inverse (hi i).leftInvOn_invFunOn
  have hmap : MapsTo (Function.invFunOn (q i) (s i)) (q i '' s i) (s i) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [(hi i).leftInvOn_invFunOn hx]
    exact hx
  apply ((hf i).comp hinv hmap).congr
  rintro _ ⟨x, hx, rfl⟩
  change f (q i (Function.invFunOn (q i) (s i) (q i x))) = f (q i x)
  rw [(hi i).leftInvOn_invFunOn hx]

end Geometry

namespace Homeomorph

theorem isFinitePL_of_parametrized_cover
    {ι : Type*} [Finite ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set F} {T : Set G} (H : S ≃ₜ T)
    (q : ∀ i, E i → F) (s : ∀ i, Set (E i))
    (hq : ∀ i, FinitePiecewiseAffineOn (q i) (s i))
    (hi : ∀ i, InjOn (q i) (s i))
    (hcover : (⋃ i, q i '' s i) = S)
    (f : ∀ i, E i → G) (hf : ∀ i, FinitePiecewiseAffineOn (f i) (s i))
    (hvalue : ∀ i (x : s i),
      (H ⟨q i x, hcover ▸ mem_iUnion.mpr ⟨i, mem_image_of_mem (q i) x.property⟩⟩ : G) =
        f i x) :
    H.IsFinitePL := by
  classical
  let g : F → G := fun x => if hx : x ∈ S then (H ⟨x, hx⟩ : G) else 0
  have hgvalue (x : S) : g x = (H x : G) := by simp only [g, dif_pos x.property]
  have hcomp (i : ι) : FinitePiecewiseAffineOn (g ∘ q i) (s i) := by
    apply (hf i).congr
    intro x hx
    have hqx : q i x ∈ S := hcover ▸ mem_iUnion.mpr ⟨i, mem_image_of_mem (q i) hx⟩
    exact (hvalue i ⟨x, hx⟩).symm.trans (hgvalue ⟨q i x, hqx⟩).symm
  refine ⟨g, ?_, fun x => (hgvalue x).symm⟩
  rw [← hcover]
  exact FinitePiecewiseAffineOn.of_parametrized_iUnion q s g hq hi hcomp

end Homeomorph
