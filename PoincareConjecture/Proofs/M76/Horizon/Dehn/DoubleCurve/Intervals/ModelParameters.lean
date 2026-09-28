import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeBranchInverse









set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "I01" => Icc (0 : ℝ) 1



theorem exists_model_interval_parameters
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {f : V2 → X} {R : Set X}
    (C : Set X) (K : SimplicialComplex ℝ E) (H : C ≃ₜ K.space)
    (F : X → E) (g : E → C)
    (hH : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {S : Set V2} (a : I01 ≃ₜ S) (ha : a.IsFinitePL)
    (hSC : MapsTo f S C) (hf : FinitePiecewiseAffineOn (F ∘ f) S)
    (hi : InjOn f S) (A B : SimplicialComplex ℝ E)
    (hA : A.space = (F ∘ f) '' S)
    (hB : ∀ z ∈ A.space, z ∈ B.space ↔ (g z : X) ∈ frontier R)
    (hboundary : ∀ u : I01, f (a u) ∈ frontier R ↔ u = 0 ∨ u = 1) :
    ∃ b : I01 ≃ₜ A.space, b.IsFinitePL ∧
      (∀ u : I01, (b u : E) = F (f (a u))) ∧
      (∀ u : I01, (g (b u) : X) = f (a u)) ∧
      A.space ∩ B.space = {(b 0 : E), (b 1 : E)} := by
  have hFi : InjOn (F ∘ f) S := by
    intro x hx y hy hxy
    apply hi hx hy
    have hHxy : H ⟨f x, hSC hx⟩ = H ⟨f y, hSC hy⟩ := by
      apply Subtype.ext
      simpa only [hH, Function.comp_apply] using hxy
    exact congrArg Subtype.val (H.injective hHxy)
  obtain ⟨q, hq, hqval⟩ := hf.exists_homeomorph_image hFi
  let q' : S ≃ₜ A.space := q.trans (Homeomorph.setCongr hA.symm)
  have hq' : q'.IsFinitePL := by
    obtain ⟨t, ht, htval⟩ := hq
    exact ⟨t, ht, htval⟩
  let b : I01 ≃ₜ A.space := a.trans q'
  have hbval (u : I01) : (b u : E) = F (f (a u)) := hqval (a u)
  have hbK (u : I01) : (b u : E) ∈ K.space := by
    rw [hbval, ← hH ⟨f (a u), hSC (a u).property⟩]
    exact (H ⟨f (a u), hSC (a u).property⟩).property
  have hgb (u : I01) : (g (b u) : X) = f (a u) := by
    have hh : (⟨(b u : E), hbK u⟩ : K.space) = H ⟨f (a u), hSC (a u).property⟩ :=
      Subtype.ext ((hbval u).trans (hH ⟨f (a u), hSC (a u).property⟩).symm)
    rw [hg ⟨b u, hbK u⟩, hh, H.symm_apply_apply]
  refine ⟨b, ha.trans hq', hbval, hgb, ?_⟩
  ext z
  constructor
  · rintro ⟨hzA, hzB⟩
    let u := b.symm ⟨z, hzA⟩
    have hu : (b u : E) = z := congrArg Subtype.val (b.apply_symm_apply ⟨z, hzA⟩)
    have huF : f (a u) ∈ frontier R := by
      rw [← hgb, hu]
      exact (hB z hzA).mp hzB
    rcases (hboundary u).mp huF with h0 | h1
    · exact Or.inl (hu.symm.trans (congrArg (fun v : I01 ↦ (b v : E)) h0))
    · exact Or.inr (hu.symm.trans (congrArg (fun v : I01 ↦ (b v : E)) h1))
  · rintro (rfl | rfl)
    · exact ⟨(b 0).property, (hB _ (b 0).property).mpr
        ((hgb 0).symm ▸ (hboundary 0).mpr (Or.inl rfl))⟩
    · exact ⟨(b 1).property, (hB _ (b 1).property).mpr
        ((hgb 1).symm ▸ (hboundary 1).mpr (Or.inr rfl))⟩

end PoincareConjecture.M76.Dehn
