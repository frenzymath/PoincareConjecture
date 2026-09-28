import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SeparatedCircleCapsRetainedDisks
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_original_polygon_parameter_cut
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) {g : E → X}
    (hg : PolyhedralPLInCharts e g (P.boundary ℝ))
    (hgi : InjOn g (P.boundary ℝ)) (hPS : g '' P.boundary ℝ ⊆ S)
    (p : S) (hp : (p : X) ∉ g '' P.boundary ℝ) :
    ∃ (m : ℕ) (R : Polygon V3 (m + 3)) (d : Fin 2 → Set V3),
      Function.Injective R ∧ R.HasSimplicialEdges ∧
      (∀ i, IsFinitePLBallPair (ℝ × ℝ) (d i) (R.boundary ℝ)) ∧
      d 0 ∪ d 1 = Sphere ∧ d 0 ∩ d 1 = R.boundary ℝ ∧
      s.map '' R.boundary ℝ = g '' P.boundary ℝ := by
  classical
  have hsval (x : Sphere) : s.map x ∈ S := by
    rw [s.map_eq x]
    exact (s.parametrization x).property
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  let q : E → V3 := fun x => if hx : x ∈ P.boundary ℝ then
    s.parametrization.symm ⟨g x,hPS ⟨x,hx,rfl⟩⟩ else 0
  have hqval (x : P.boundary ℝ) :
      q x = (s.parametrization.symm ⟨g x,hPS ⟨x,x.property,rfl⟩⟩ : V3) := by
    simp only [q,dif_pos x.property]
  have hqS : MapsTo q (P.boundary ℝ) Sphere := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (s.parametrization.symm ⟨g x,hPS ⟨x,hx,rfl⟩⟩).property
  have hvalue (x : E) (hx : x ∈ P.boundary ℝ) : s.map (q x) = g x := by
    rw [hqval ⟨x,hx⟩,s.map_eq]
    exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨g x,hPS ⟨x,hx,rfl⟩⟩)
  have hqcont : ContinuousOn q (P.boundary ℝ) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (s.parametrization.symm.continuous.comp
      (hg.continuousOn.domRestrict.subtype_mk (fun x => hPS ⟨x,x.property,rfl⟩)))
    convert h using 1
    funext x
    exact hqval x
  let A := P.simplicialComplex hP
  have hA := P.finite_simplicialComplex_faces hP
  have hAs : A.space = P.boundary ℝ := P.simplicialComplex_space hP
  have hq : FinitePiecewiseAffineOn q (P.boundary ℝ) := by
    rw [←hAs]
    apply s.piecewiseAffine.finitePiecewiseAffineOn_lift he hsi A hA
      (hqcont.mono hAs.subset) (fun _ hx => hqS (hAs.subset hx))
    exact (hAs.symm ▸ hg).congr (fun x hx => (hvalue x (hAs.subset hx)).symm)
  have hqi : InjOn q (P.boundary ℝ) := by
    intro x hx y hy hxy
    apply hgi hx hy
    rw [←hvalue x hx,←hvalue y hy,hxy]
  obtain ⟨m,R,hRi,hR,hRr⟩ := P.exists_polygon_finitePL_image hP hPi hq subset_rfl hqi
  have hRS : R.boundary ℝ ⊆ Sphere := by
    rw [hRr]
    exact image_subset_iff.mpr hqS
  let pole := s.parametrization.symm p
  have hpole : (pole : V3) ∉ R.boundary ℝ := by
    rw [hRr]
    rintro ⟨x,hx,hxp⟩
    apply hp
    refine ⟨x,hx,?_⟩
    rw [←hvalue x hx,hxp,s.map_eq pole]
    exact congrArg Subtype.val (s.parametrization.apply_symm_apply p)
  obtain ⟨K,hK,hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hfront : Sphere = frontier (closedBall (0 : V3) 1) := by
    rw [frontier_closedBall _ one_ne_zero]
  obtain ⟨d0,d1,hd0,hd1,hwhole,hinter,_⟩ := K.exists_convex_sphere_polygon_cut hK
    (isCompact_closedBall (0 : V3) 1) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    (hKs.trans hfront) (by simp) R hR hRi (hRS.trans hfront.subset)
    ⟨pole,hfront.subset pole.property⟩ hpole
  refine ⟨m,R,![d0,d1],hRi,hR,?_,hwhole.trans hfront.symm,hinter,?_⟩
  · intro i
    fin_cases i <;> assumption
  · rw [hRr,image_image]
    exact image_congr (fun x hx => hvalue x hx)

end PoincareConjecture.M76
