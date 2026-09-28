import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningFaceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_triangle_plane_coordinates
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] (ℝ × ℝ)),
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (affineSpan ℝ (A '' (s : Set E))) := by
  classical
  let K₀ : SimplicialComplex ℝ E :=
    { faces := {b | b ∈ K.faces ∧ b ⊆ s}
      indep := fun hb => K.indep hb.1
      isRelLowerSet_faces := by
        intro b hb
        exact ⟨K.nonempty_of_mem_faces hb.1, fun c hcb hc =>
          ⟨K.down_closed hb.1 hcb hc, hcb.trans hb.2⟩⟩
      inter_subset_convexHull := fun hb hc => K.inter_subset_convexHull hb.1 hc.1 }
  have hs₀ : s ∈ K₀.faces := ⟨hs, Finset.Subset.rfl⟩
  have hK₀s : K₀.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hxb⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono hb.2 hxb
    · exact K₀.convexHull_subset_space hs₀
  have hAi : InjOn A K₀.space := by
    intro x hx y hy hxy
    have hx' := hK₀s.subset hx
    have hy' := hK₀s.subset hy
    exact hgi (K.convexHull_subset_space hs hx') (K.convexHull_subset_space hs hy')
      (Q.injOn (hmap hx') (hmap hy') ((hA hx').trans (hxy.trans (hA hy').symm)))
  have hf : K₀.AffineOnFaces A := K₀.affineOnFaces_affine A
  let T₀ := hf.embeddedImage hAi
  have ht : s.image A ∈ T₀.faces :=
    (hf.embeddedImage_faces hAi).symm ▸ mem_image_of_mem (fun t : Finset E => t.image A) hs₀
  have ht3 : (s.image A).card = 3 := by
    rw [Finset.card_image_of_injOn (hAi.mono (K₀.subset_space hs₀)), hs3]
  obtain ⟨v0, v1, v2, h01, h02, h12, hverts⟩ := Finset.card_eq_three.mp ht3
  have hface : ({v0, v1, v2} : Set V3) = A '' (s : Set E) := by
    simpa only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton] using
      (congrArg (fun t : Finset V3 => (t : Set V3)) hverts).symm
  obtain ⟨F, R, hRF, hFR, _⟩ := T₀.exists_returning_face_coordinates h01 h02 h12 (by
    convert ht using 1
    ext x
    simp only [hverts, Finset.mem_insert, Finset.mem_singleton])
  refine ⟨F, R, hRF, ?_⟩
  simpa only [hface] using hFR

end PoincareConjecture.M76
