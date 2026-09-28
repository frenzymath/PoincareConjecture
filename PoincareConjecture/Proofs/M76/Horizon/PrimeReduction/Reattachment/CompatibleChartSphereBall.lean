import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalConfinedSphereBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ChartwiseBall
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Sphere

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Cube" => closedBall (0 : V3) 1

theorem ChartwisePLSphere.exists_ball_in_compatible_unit_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hsource : S ⊆ Q.source) (htarget : Q.target = ball (0 : V3) 1) :
    ∃ B : Set X, B ⊆ Q.source ∧ Nonempty (ChartwisePLBall e B S) := by
  obtain ⟨A,hA,hAS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hmap (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  have hf : FinitePiecewiseAffineOn (Q ∘ s.map) Sphere := by
    rw [←hAS]
    exact (hAS.symm ▸ s.piecewiseAffine).finitePiecewiseAffineOn_compatible_chart_finite_source
      A hA Q hQ (fun x hx => hsource (hmap x (hAS.subset hx)))
  have hfi : InjOn (Q ∘ s.map) Sphere := by
    intro x hx y hy hxy
    have hm := Q.injOn (hsource (hmap x hx)) (hsource (hmap y hy)) hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hm
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hm))
  have himage : (Q ∘ s.map) '' Sphere = Q '' S := by
    rw [image_comp]
    congr 1
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hmap x hx
    · intro x hx
      let y := s.parametrization.symm ⟨x,hx⟩
      refine ⟨y,y.property,?_⟩
      rw [s.map_eq y]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨x,hx⟩)
  obtain ⟨H,hH,_⟩ := hf.exists_homeomorph_image hfi
  have hchart : ∃ G : (Q '' S) ≃ₜ frontier Cube, G.IsFinitePL := by
    rw [←himage,frontier_closedBall _ one_ne_zero]
    exact ⟨H.symm,hH.symm⟩
  obtain ⟨G,hG⟩ := hchart
  obtain ⟨K,_,hK,hKC,_,_⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 3)).exists_finite_carrier_and_rim_complexes
  have hinside : Q '' S ⊆ interior Cube := by
    rintro _ ⟨x,hx,rfl⟩
    exact ball_subset_interior_closedBall (htarget ▸ Q.map_source (hsource hx))
  obtain ⟨U,_,_,_,hUC,hUB,_⟩ := hG.hasAlexanderRegionBalls
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp) (by simp)
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hinside K hK hKC
  have hUQ : closure U ⊆ Q.target := by
    rw [htarget,←interior_closedBall _ one_ne_zero]
    exact hUC
  have hball := chartwisePLBall_of_finitePLBallPair_in_chart e Q hcover hQ
    (ContinuousLinearEquiv.ofFinrankEq (by simp)) hUB hUQ
  have hback : Q.symm '' (Q '' S) = S := Q.symm_image_image_of_subset_source hsource
  rw [hback] at hball
  refine ⟨Q.symm '' closure U,?_,hball⟩
  rintro _ ⟨x,hx,rfl⟩
  exact Q.map_target (hUQ hx)

theorem exists_ball_of_annulus_and_disks_in_unit_chart
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (htarget : Q.target = ball (0 : V3) 1)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4*d < L)
    {g : (ℝ × ℝ) → X} {f₀ : E → X} {f₁ : F → X}
    {c₀ q₀ : Set E} {c₁ q₁ : Set F}
    (hg : PolyhedralPLInCharts e g (PLAnnularStrip.squareAnnulus L d))
    (hgi : InjOn g (PLAnnularStrip.squareAnnulus L d))
    (hc₀ : IsFinitePLBallPair (ℝ × ℝ) c₀ q₀)
    (hc₁ : IsFinitePLBallPair (ℝ × ℝ) c₁ q₁)
    (hf₀ : PolyhedralPLInCharts e f₀ c₀) (hf₁ : PolyhedralPLInCharts e f₁ c₁)
    (hi₀ : InjOn f₀ c₀) (hi₁ : InjOn f₁ c₁)
    (hrim₀ : g '' frontier (_root_.Dehn.annulusSquare L (-d)) = f₀ '' q₀)
    (hrim₁ : g '' frontier (_root_.Dehn.annulusSquare L d) = f₁ '' q₁)
    (hcontact₀ : (g '' PLAnnularStrip.squareAnnulus L d) ∩ (f₀ '' c₀) = f₀ '' q₀)
    (hcontact₁ : (g '' PLAnnularStrip.squareAnnulus L d) ∩ (f₁ '' c₁) = f₁ '' q₁)
    (hdis : Disjoint (f₀ '' c₀) (f₁ '' c₁))
    (hgQ : g '' PLAnnularStrip.squareAnnulus L d ⊆ Q.source)
    (hf₀Q : f₀ '' c₀ ⊆ Q.source) (hf₁Q : f₁ '' c₁ ⊆ Q.source) :
    ∃ B : Set X, B ⊆ Q.source ∧ Nonempty (ChartwisePLBall e B
      ((g '' PLAnnularStrip.squareAnnulus L d) ∪ ((f₀ '' c₀) ∪ (f₁ '' c₁)))) := by
  obtain ⟨s⟩ := Dehn.Annuli.CyclicPanels.nonempty_original_sphere_of_annulus_and_disks
    he hd hwidth hg hgi hc₀ hc₁ hf₀ hf₁ hi₀ hi₁ hrim₀ hrim₁
    hcontact₀ hcontact₁ hdis
  exact s.exists_ball_in_compatible_unit_chart Q hcover hQ
    (union_subset hgQ (union_subset hf₀Q hf₁Q)) htarget

end PoincareConjecture.M76
