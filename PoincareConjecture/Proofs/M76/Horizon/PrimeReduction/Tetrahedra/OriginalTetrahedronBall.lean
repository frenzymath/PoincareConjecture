import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem isFinitePLBallPair_independent_tetrahedron
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 4) :
    IsFinitePLBallPair (Fin 3 → ℝ) (convexHull ℝ (s : Set E))
      (intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) := by
  classical
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (k := ℝ) (P := Fin 3 → ℝ) (ι := s) (by simpa using hcard)
  let F₀ : (Fin 3 → ℝ) →ᵃ[ℝ] E :=
    (Fintype.linearCombination ℝ (Subtype.val : s → E)).toAffineMap.comp b.coords
  let F : (Fin 3 → ℝ) →ᴬ[ℝ] E := ⟨F₀,F₀.continuous_of_finiteDimensional⟩
  have hF (i : s) : F (b i) = (i : E) := by
    simp [F,F₀,Fintype.linearCombination_apply,AffineBasis.coords_apply,AffineBasis.coord_apply]
  let r : E → (Fin 3 → ℝ) := fun x => if hx : x ∈ s then b ⟨x,hx⟩ else 0
  obtain ⟨R,hR⟩ := hind.exists_continuousAffineMap_eqOn r
  have hRi (i : s) : R i = b i := by simpa [r,i.property] using hR i.property
  have hRF : R.toAffineMap.comp F.toAffineMap = AffineMap.id ℝ (Fin 3 → ℝ) := by
    apply AffineMap.ext_on b.tot
    rintro _ ⟨i,rfl⟩
    change R (F (b i)) = b i
    rw [hF,hRi]
  have hleft : Function.LeftInverse R F := fun x => congrArg (fun a => a x) hRF
  let u : Finset (Fin 3 → ℝ) := Finset.univ.image b
  have hu : (u : Set (Fin 3 → ℝ)) = range b := by simp [u]
  have hui : AffineIndependent ℝ ((↑) : u → (Fin 3 → ℝ)) := by
    change AffineIndependent ℝ ((↑) : ↥(u : Set (Fin 3 → ℝ)) → (Fin 3 → ℝ))
    rw [hu]
    exact b.ind.range
  let Δ := convexHull ℝ (u : Set (Fin 3 → ℝ))
  have hspan : affineSpan ℝ Δ = ⊤ := by
    dsimp only [Δ]
    rw [affineSpan_convexHull,hu,b.tot]
  have hΔne : (interior Δ).Nonempty :=
    (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hverts : F '' (u : Set (Fin 3 → ℝ)) = (s : Set E) := by
    rw [hu]
    apply Subset.antisymm
    · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      exact hF i ▸ i.property
    · intro x hx
      exact ⟨b ⟨x,hx⟩,mem_range_self _,hF ⟨x,hx⟩⟩
  have htarget : F '' Δ = convexHull ℝ (s : Set E) :=
    (F.toAffineMap.image_convexHull _).trans (congrArg (convexHull ℝ) hverts)
  have hboundary : intrinsicFrontier ℝ Δ = frontier Δ := by
    let H : (affineSpan ℝ Δ : Set (Fin 3 → ℝ)) ≃ₜ (Fin 3 → ℝ) :=
      (Homeomorph.setCongr (show (affineSpan ℝ Δ : Set (Fin 3 → ℝ)) = univ by
        rw [hspan]; rfl)).trans (Homeomorph.Set.univ _)
    change H '' frontier (H ⁻¹' Δ) = frontier Δ
    rw [H.image_frontier,H.surjective.image_preimage]
  have hfront : F '' frontier Δ = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    have h := F.toAffineMap.intrinsicFrontier_image_of_injOn Δ hleft.injective.injOn
    change intrinsicFrontier ℝ (F '' Δ) = F '' intrinsicFrontier ℝ Δ at h
    rw [htarget,hboundary] at h
    exact h.symm
  have hmodel := (isFinitePLBallPair_convexHull_finset u hui hΔne).affine_image F hleft.injective.injOn
  change IsFinitePLBallPair (Fin 3 → ℝ) (F '' Δ) (F '' frontier Δ) at hmodel
  rwa [htarget,hfront] at hmodel

theorem vertex_mem_intrinsicFrontier_independent_tetrahedron
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 4)
    {v : E} (hv : v ∈ s) : v ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  have hproper : ({v} : Finset E) ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.singleton_subset_iff.mpr hv,fun h => by
      have hc := congrArg Finset.card h
      simp only [Finset.card_singleton,hcard] at hc
      omega⟩
  apply hind.convexHull_subset_intrinsicFrontier hproper
  simpa only [Finset.coe_singleton] using subset_convexHull ℝ ({v} : Set E) (mem_singleton v)

end PoincareConjecture.M76
