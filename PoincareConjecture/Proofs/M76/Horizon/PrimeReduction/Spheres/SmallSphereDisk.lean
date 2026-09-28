import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereDisks
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexNeighborhood










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]




theorem IsFinitePL.exists_small_local_ball_pairs_of_convex_frontier
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V + 1) (x : s)
    {U : Set E} (hU : IsOpen U) (hxU : (x : E) ∈ U) :
    ∃ d q : Set E, IsFinitePLBallPair V d q ∧ d ⊆ s ∩ U ∧
      (x : E) ∈ d \ q ∧ IsOpen ((Subtype.val : s → E) ⁻¹' (d \ q)) := by
  obtain ⟨D, R, hD, hDs, hxD, hopen⟩ :=
    he.exists_local_ball_pairs_of_convex_frontier hC hcv hne hdim x
  obtain ⟨_, A, hA, hAcv, _, g, hg, hgR⟩ := hD
  let z : A := g ⟨x, hxD.1⟩
  have hzint : (z : V) ∈ interior A := by
    by_contra hz
    exact hxD.2 ((hgR ⟨x, hxD.1⟩).mpr ⟨subset_closure z.property, hz⟩)
  let O : Set A := g.symm ⁻¹' ((Subtype.val : D → E) ⁻¹' U)
  have hO : IsOpen O := (hU.preimage continuous_subtype_val).preimage g.symm.continuous
  have hzO : z ∈ O := by simpa [O, z] using hxU
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hO
  have hzW : (z : V) ∈ W := (Set.ext_iff.mp hWeq z).mpr hzO
  obtain ⟨K, hK, hKcv, hzK, hKW⟩ :=
    (isOpen_interior.inter hW).exists_finite_convex_neighborhood ⟨hzint, hzW⟩
  have hKA : K.space ⊆ A := fun y hy => interior_subset (hKW hy).1
  have hpair : IsFinitePLBallPair V K.space (frontier K.space) :=
    isFinitePLBallPair_of_compact_convex (K.isCompact_space_of_finite hK)
      hKcv ⟨z, hzK⟩ K hK rfl
  obtain ⟨f, hfPL, hf⟩ := hg
  let d : Set E := D ∩ f ⁻¹' K.space
  let q : Set E := D ∩ f ⁻¹' frontier K.space
  have hgPL : g.IsFinitePL := ⟨f, hfPL, hf⟩
  have hd : IsFinitePLBallPair V d q := hgPL.preimage_ballPair hpair hKA hf
  have hdq : d \ q = D ∩ f ⁻¹' interior K.space := by
    rw [← self_sdiff_frontier K.space]
    ext y
    simp only [d, q, mem_sdiff, mem_inter_iff, mem_preimage]
    tauto
  have hdDR : d ⊆ D \ R := by
    rintro y ⟨hyD, hyK⟩
    refine ⟨hyD, ?_⟩
    intro hyR
    apply ((hgR ⟨y, hyD⟩).mp hyR).2
    rw [hf]
    exact (hKW hyK).1
  have hdU : d ⊆ U := by
    rintro y ⟨hyD, hyK⟩
    have hyO : g ⟨y, hyD⟩ ∈ O := (Set.ext_iff.mp hWeq (g ⟨y, hyD⟩)).mp (by
      change (g ⟨y, hyD⟩ : V) ∈ W
      rw [hf]
      exact (hKW hyK).2)
    simpa [O] using hyO
  have hx : (x : E) ∈ d \ q := by
    rw [hdq]
    refine ⟨hxD.1, ?_⟩
    change f x ∈ interior K.space
    rw [← hf ⟨x, hxD.1⟩]
    exact hzK
  have hopenD : IsOpen ((Subtype.val : D → E) ⁻¹' (d \ q)) := by
    have heq : (Subtype.val : D → E) ⁻¹' (d \ q) =
        g ⁻¹' ((Subtype.val : A → V) ⁻¹' interior K.space) := by
      rw [hdq]
      ext y
      simp only [mem_preimage, mem_inter_iff, y.property, true_and, hf]
    rw [heq]
    exact (isOpen_interior.preimage continuous_subtype_val).preimage g.continuous
  obtain ⟨N, hN, hNeq⟩ := isOpen_induced_iff.mp hopenD
  have hsmall : (Subtype.val : s → E) ⁻¹' (d \ q) =
      (Subtype.val : s → E) ⁻¹' (D \ R) ∩ (Subtype.val : s → E) ⁻¹' N := by
    ext y
    constructor
    · intro hy
      have hyDR := hdDR hy.1
      exact ⟨hyDR, (Set.ext_iff.mp hNeq ⟨y, hyDR.1⟩).mpr hy⟩
    · rintro ⟨hyDR, hyN⟩
      exact (Set.ext_iff.mp hNeq ⟨y, hyDR.1⟩).mp hyN
  refine ⟨d, q, hd, fun y hy => ⟨hDs (hdDR hy).1, hdU hy⟩, hx, ?_⟩
  rw [hsmall]
  exact hopen.inter (hN.preimage continuous_subtype_val)

end Homeomorph
