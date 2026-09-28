import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapProductCoordinates

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.exists_original_oriented_centered_product_coordinates
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ I)) (hci : InjOn c (N.space ×ˢ I))
    (hzero : c '' (N.space ×ˢ {(0 : ℝ)}) = S) (positive : Bool) :
    ∃ F : V3 × ℝ → X,
      PolyhedralPLInCharts e F (Sphere ×ˢ I) ∧ InjOn F (Sphere ×ˢ I) ∧
      (∀ x ∈ Sphere, F (x,0) = s.map x) ∧
      ∀ A : Set ℝ, F '' (Sphere ×ˢ A) =
        c '' (N.space ×ˢ ((fun t : ℝ => if positive then t else -t) '' A)) := by
  obtain ⟨F,hF,hFi,hFzero,hFimage⟩ :=
    s.exists_original_centered_product_coordinates hcompat N hN c hc hci hzero
  cases positive
  case true =>
    refine ⟨F,hF,hFi,hFzero,?_⟩
    intro A
    simpa using hFimage A
  case false =>
    obtain ⟨K,hK,hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
    obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ :=
      isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
    obtain ⟨M,hM,hMs,_⟩ := K.exists_finite_triangulation_prod L hK hL
    have hMs' : M.space = Sphere ×ˢ I := by simpa only [hKs,hLs] using hMs
    let a : V3 × ℝ →ᴬ[ℝ] V3 × ℝ :=
      (ContinuousLinearMap.fst ℝ V3 ℝ).toContinuousAffineMap.prod
        (-(ContinuousLinearMap.snd ℝ V3 ℝ).toContinuousAffineMap)
    have ha : FinitePiecewiseAffineOn a M.space :=
      ⟨M,hM,rfl,M.affineOnFaces_affine a⟩
    have hmap : MapsTo a M.space (Sphere ×ˢ I) := by
      intro z hz
      have hz' := hMs'.subset hz
      exact ⟨hz'.1,by dsimp [a]; linarith [hz'.2.2],by dsimp [a]; linarith [hz'.2.1]⟩
    let G := F ∘ a
    have hG : PolyhedralPLInCharts e G (Sphere ×ˢ I) :=
      hMs' ▸ hF.comp_finitePiecewiseAffineOn M hM ha hmap
    have hGi : InjOn G (Sphere ×ˢ I) := by
      intro z hz w hw hzw
      have h := hFi (hmap (hMs'.symm.subset hz)) (hmap (hMs'.symm.subset hw)) hzw
      apply Prod.ext
      · have hx := congrArg (fun p : V3 × ℝ => p.1) h
        exact hx
      · have ht := congrArg (fun p : V3 × ℝ => p.2) h
        change -z.2 = -w.2 at ht
        exact neg_injective ht
    refine ⟨G,hG,hGi,?_,?_⟩
    · intro x hx
      change F (x,-0) = s.map x
      simpa only [neg_zero] using hFzero x hx
    · intro A
      rw [←hFimage]
      apply Subset.antisymm
      · rintro _ ⟨z,hz,rfl⟩
        exact ⟨(z.1,-z.2),⟨hz.1,⟨z.2,hz.2,rfl⟩⟩,rfl⟩
      · rintro _ ⟨z,⟨hz,⟨t,ht,hteq⟩⟩,rfl⟩
        exact ⟨(z.1,t),⟨hz,ht⟩,by change F (z.1,-t) = F z; rw [show -t = z.2 from hteq]⟩

end PoincareConjecture.M76
