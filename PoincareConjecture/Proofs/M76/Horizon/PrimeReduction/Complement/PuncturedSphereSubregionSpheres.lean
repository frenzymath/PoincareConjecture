import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SphereModelCap

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_finitePL_parent_model_image
    {X E F ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {S R : Set X} {M : Set E} {Q : Set F}
    (s : ChartwisePLSphere e S) (hSR : S ⊆ R)
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (G : R ≃ₜ M) (hG : ∀ x : R, (G x : E) = f x)
    (C : M ≃ₜ Q) (hC : C.IsFinitePL) :
    ∃ H : ((fun x : R => (C (G x) : F)) ''
        ((Subtype.val : R → X) ⁻¹' S)) ≃ₜ frontier (closedBall (0 : V3) 1),
      H.IsFinitePL := by
  have hfi : InjOn f R := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hG ⟨x, hx⟩).trans (hxy.trans (hG ⟨y, hy⟩).symm))))
  obtain ⟨P, hP, _⟩ := s.exists_finitePL_model_parametrization f hf (hfi.mono hSR) rfl
  obtain ⟨g, hg, hCg⟩ := hC
  obtain ⟨p, hp, hPp⟩ := hP
  have hpM : MapsTo p (sphere (0 : V3) 1) M := by
    intro x hx
    rw [← hPp ⟨x, hx⟩]
    obtain ⟨y, hy, hfy⟩ := (P ⟨x, hx⟩).property
    exact hfy ▸ (hG ⟨y, hSR hy⟩ ▸ (G ⟨y, hSR hy⟩).property)
  have hgi : InjOn g M := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (C.injective (Subtype.ext
      ((hCg ⟨x, hx⟩).trans (hxy.trans (hCg ⟨y, hy⟩).symm))))
  have hpi : InjOn p (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (P.injective (Subtype.ext
      ((hPp ⟨x, hx⟩).trans (hxy.trans (hPp ⟨y, hy⟩).symm))))
  obtain ⟨H, hH, _⟩ := (hg.comp hp hpM).exists_homeomorph_image
    (hgi.comp hpi hpM)
  have himage : (g ∘ p) '' sphere (0 : V3) 1 =
      (fun x : R => (C (G x) : F)) '' ((Subtype.val : R → X) ⁻¹' S) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hfy⟩ := (P ⟨x, hx⟩).property
      refine ⟨⟨y, hSR hy⟩, hy, ?_⟩
      change (C (G ⟨y, hSR hy⟩) : F) = g (p x)
      rw [hCg, hG]
      exact congrArg g (hfy.trans (hPp ⟨x, hx⟩))
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := P.surjective ⟨f x, mem_image_of_mem f hx⟩
      refine ⟨y, y.property, ?_⟩
      change g (p y) = (C (G x) : F)
      rw [hCg, hG, ← hPp y, hy]
  exact ⟨(Homeomorph.setCongr himage.symm).trans
      (H.symm.trans (Homeomorph.setCongr (frontier_closedBall _ one_ne_zero).symm)),
    hH.symm.setCongr himage (frontier_closedBall _ one_ne_zero).symm⟩

end PoincareConjecture.M76
