import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedGraphImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem finitePLBallPair_original_image
    {X ι E M G : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3} {D bd Z : Set E} {R : Set X}
    {p : E → X} {F : X → G}
    (hD : IsFinitePLBallPair M D bd) (hp : PolyhedralPLInCharts e p Z)
    (hDZ : D ⊆ Z) (hpi : InjOn p Z) (hpR : MapsTo p D R)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F R) :
    IsFinitePLBallPair M (F '' (p '' D)) (F '' (p '' bd)) := by
  have hDcopy := hD
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hDcopy
  have hcomp : FinitePiecewiseAffineOn (F ∘ p) D := by
    rw [←hKs]
    exact (hp.restrict_finite K hK (hKs.subset.trans hDZ)).finitePiecewiseAffineOn_comp
      K hK hF
  have hcompi : InjOn (F ∘ p) D := by
    intro x hx y hy hxy
    exact hpi (hDZ hx) (hDZ hy) (hFi (hpR hx) (hpR hy) hxy)
  simpa only [image_comp] using hD.image hcomp hcompi

theorem ChartwisePLBall.finitePLBallPair_image
    {X ι G : Type*} [TopologicalSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3} {D bd R : Set X}
    (b : ChartwisePLBall e D bd) (hDR : D ⊆ R) (F : X → G)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F R) :
    IsFinitePLBallPair V3 (F '' D) (F '' bd) := by
  have hmapD : b.map '' closedBall (0 : V3) 1 = D := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [b.map_eq ⟨x,hx⟩]
      exact (b.parametrization ⟨x,hx⟩).property
    · intro x hx
      obtain ⟨z,hz⟩ := b.parametrization.surjective ⟨x,hx⟩
      exact ⟨z,z.property,(b.map_eq z).trans (congrArg Subtype.val hz)⟩
  have hmapbd : b.map '' sphere (0 : V3) 1 = bd := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      let z : closedBall (0 : V3) 1 := ⟨x,sphere_subset_closedBall hx⟩
      rw [b.map_eq z]
      exact (b.boundary_eq z).mpr hx
    · intro x hx
      obtain ⟨z,hz⟩ := b.parametrization.surjective ⟨x,b.boundary_subset hx⟩
      have hzbd : (b.parametrization z : X) ∈ bd := by rw [hz]; exact hx
      exact ⟨z,(b.boundary_eq z).mp hzbd,
        (b.map_eq z).trans (congrArg Subtype.val hz)⟩
  have hbi : InjOn b.map (closedBall (0 : V3) 1) := by
    intro x hx y hy hxy
    rw [b.map_eq ⟨x,hx⟩,b.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (b.parametrization.injective (Subtype.ext hxy))
  have hpR : MapsTo b.map (closedBall (0 : V3) 1) R := by
    intro x hx
    exact hDR (hmapD.subset ⟨x,hx,rfl⟩)
  simpa only [hmapD,hmapbd] using finitePLBallPair_original_image
    (isFinitePLBallPair_unit_cube (ι := Fin 3)) b.piecewiseAffine subset_rfl hbi hpR hF hFi

end PoincareConjecture.M76
