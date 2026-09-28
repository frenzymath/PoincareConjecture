import PoincareConjecture.Proofs.M76.Triangulation.ConvexSpherePolygonCut










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem IsFinitePL.exists_polygon_cut {s : Set E} {C : Set F}
    {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPs : P.boundary ℝ ⊆ s) (p : s) (hp : (p : E) ∉ P.boundary ℝ) :
    ∃ b c : Set E, IsFinitePLBallPair (ℝ × ℝ) b (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) c (P.boundary ℝ) ∧ b ∪ c = s ∧
      b ∩ c = P.boundary ℝ ∧ (p : E) ∈ c \ P.boundary ℝ := by
  have hecopy := he
  obtain ⟨f, hf, heval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  have hgf : LeftInvOn g f s := by
    intro x hx
    rw [← heval ⟨x, hx⟩, ← hgval, e.symm_apply_apply]
  have hfg : LeftInvOn f g (frontier C) := by
    intro y hy
    rw [← hgval ⟨y, hy⟩, ← heval, e.apply_symm_apply]
  obtain ⟨N, R, hRi, hRs, hRb⟩ :=
    P.exists_polygon_finitePL_image hP hinj hf hPs (hgf.injOn.mono hPs)
  have hRsub : R.boundary ℝ ⊆ frontier C := by
    rw [hRb]
    rintro _ ⟨x, hx, rfl⟩
    rw [← heval ⟨x, hPs hx⟩]
    exact (e ⟨x, hPs hx⟩).property
  have hpR : (e p : F) ∉ R.boundary ℝ := by
    rw [hRb]
    rintro ⟨x, hx, hxp⟩
    rw [heval] at hxp
    have heq := hgf.injOn (hPs hx) p.property hxp
    exact hp (heq ▸ hx)
  have hgcopy := hg
  obtain ⟨K, hK, hKC, _⟩ := hgcopy
  obtain ⟨b, c, hb, hc, hunion, hinter, hpc⟩ :=
    K.exists_convex_sphere_polygon_cut hK hC hcv hne hKC hdim R hRs hRi hRsub (e p) hpR
  have hbC : b ⊆ frontier C := fun x hx => hunion ▸ Or.inl hx
  have hcC : c ⊆ frontier C := fun x hx => hunion ▸ Or.inr hx
  have hback : g '' R.boundary ℝ = P.boundary ℝ := by
    rw [hRb]
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      rw [hgf (hPs hy)] at hxy
      exact hxy ▸ hy
    · intro hx
      exact ⟨f x, mem_image_of_mem f hx, hgf (hPs hx)⟩
  have hb' := hb.image_of_subset hg hbC hfg.injOn
  have hc' := hc.image_of_subset hg hcC hfg.injOn
  rw [hback] at hb' hc'
  refine ⟨g '' b, g '' c, hb', hc', ?_, ?_, ?_⟩
  · rw [← image_union, hunion]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hgval ⟨y, hy⟩]
      exact (e.symm ⟨y, hy⟩).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, (e ⟨x, hx⟩).property, ?_⟩
      rw [← hgval, e.symm_apply_apply]
  · rw [← hfg.injOn.image_inter hbC hcC, hinter, hback]
  · refine ⟨⟨e p, hpc.1, ?_⟩, hp⟩
    rw [← hgval, e.symm_apply_apply]

end Homeomorph
