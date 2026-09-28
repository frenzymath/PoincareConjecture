import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSurfaceComplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Cube" => closedBall (0 : V3) 1

theorem ChartwisePLSphere.exists_original_confined_ball
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {S B R : Set X} (s : ChartwisePLSphere e S) (b : ChartwisePLBall e B R)
    (hSB : S ⊆ interior B) :
    ∃ D : Set X, D ⊆ interior B ∧ Nonempty (ChartwisePLBall e D S) := by
  classical
  have hsS (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  have hbi : InjOn b.map Cube := by
    intro x hx y hy hxy
    rw [b.map_eq ⟨x,hx⟩,b.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (b.parametrization.injective (Subtype.ext hxy))
  let q : V3 → V3 := fun x => if hx : x ∈ Sphere then
    b.parametrization.symm ⟨s.map x,interior_subset (hSB (hsS x hx))⟩ else 0
  have hqval (x : Sphere) : q x =
      (b.parametrization.symm ⟨s.map x,interior_subset (hSB (hsS x x.property))⟩ : V3) := by
    simp only [q,dif_pos x.property]
  have hqCube : MapsTo q Sphere Cube := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (b.parametrization.symm ⟨s.map x,interior_subset (hSB (hsS x hx))⟩).property
  have hvalue (x : V3) (hx : x ∈ Sphere) : b.map (q x) = s.map x := by
    rw [hqval ⟨x,hx⟩,b.map_eq]
    exact congrArg Subtype.val (b.parametrization.apply_symm_apply _)
  have hqc : ContinuousOn q Sphere := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (b.parametrization.symm.continuous.comp
      (s.piecewiseAffine.continuousOn.domRestrict.subtype_mk
        (fun x => interior_subset (hSB (hsS x x.property)))))
    convert h using 1
    funext x
    exact hqval x
  obtain ⟨A,hA,hAS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hq : FinitePiecewiseAffineOn q Sphere := by
    rw [←hAS]
    exact b.piecewiseAffine.finitePiecewiseAffineOn_lift he hbi A hA
      (hqc.mono hAS.subset) (fun x hx => hqCube (hAS.subset hx))
      ((s.piecewiseAffine.restrict_finite A hA hAS.subset).congr
        (fun x hx => (hvalue x (hAS.subset hx)).symm))
  have hqi : InjOn q Sphere := by
    intro x hx y hy hxy
    have heq := congrArg b.map hxy
    rw [hvalue x hx,hvalue y hy,s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at heq
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext heq))
  have hqint : q '' Sphere ⊆ interior Cube := by
    rintro _ ⟨x,hx,rfl⟩
    by_contra hn
    have hfront : q x ∈ frontier Cube := ⟨subset_closure (hqCube hx),hn⟩
    rw [frontier_closedBall _ one_ne_zero] at hfront
    have hR := (b.boundary_eq ⟨q x,hqCube hx⟩).mpr hfront
    rw [←b.map_eq,hvalue x hx,←b.frontier_eq] at hR
    exact hR.2 (hSB (hsS x hx))
  obtain ⟨H,hH,_⟩ := hq.exists_homeomorph_image hqi
  have hchart : ∃ G : (q '' Sphere) ≃ₜ frontier Cube, G.IsFinitePL := by
    rw [frontier_closedBall _ one_ne_zero]
    exact ⟨H.symm,hH.symm⟩
  obtain ⟨G,hG⟩ := hchart
  obtain ⟨K,_,hK,hKC,_,_⟩ :=
    Set.IsFinitePLBallPair.exists_finite_carrier_and_rim_complexes
      (isFinitePLBallPair_unit_cube (ι := Fin 3))
  obtain ⟨U,_,_,_,hUC,hUB,_⟩ := hG.hasAlexanderRegionBalls
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp) (by simp)
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hqint K hK hKC
  have hback : b.map '' (q '' Sphere) = S := by
    apply Subset.antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      rw [hvalue x hx]
      exact hsS x hx
    · intro x hx
      let y := s.parametrization.symm ⟨x,hx⟩
      refine ⟨q y,⟨y,y.property,rfl⟩,?_⟩
      rw [hvalue y y.property,s.map_eq y]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨x,hx⟩)
  have hball := exists_chartwisePLBall_image hUB
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]))
    b.piecewiseAffine (hUC.trans interior_subset) hbi
  rw [hback] at hball
  refine ⟨b.map '' closure U,?_,hball⟩
  rintro _ ⟨x,hx,rfl⟩
  rw [b.interior_eq_sdiff,b.map_eq ⟨x,interior_subset (hUC hx)⟩]
  refine ⟨(b.parametrization ⟨x,interior_subset (hUC hx)⟩).property,?_⟩
  intro hR
  have hsphere := (b.boundary_eq ⟨x,interior_subset (hUC hx)⟩).mp hR
  rw [←frontier_closedBall _ one_ne_zero] at hsphere
  exact hsphere.2 (hUC hx)

end PoincareConjecture.M76
