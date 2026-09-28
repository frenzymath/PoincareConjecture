import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCubeBoundaryPush
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization










set_option autoImplicit false

open Set Metric Geometry

namespace Set

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]





theorem IsFinitePLBallPair.exists_push_fixing_boundary_polyhedron
    {C S : Set E} (hC : IsFinitePLBallPair V C S) (hdim : Module.finrank ℝ V = 3)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJS : J.space ⊆ S) :
    ∃ f : E → E, FinitePiecewiseAffineOn f C ∧ InjOn f C ∧ MapsTo f C C ∧
      EqOn f id J.space ∧ ∀ x ∈ C, f x ∈ S ↔ x ∈ J.space := by
  let a : V ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨e, he, heb⟩ := hC.exists_cube_chart a
  have heb' (x : C) : (x : E) ∈ S ↔ (e x : Fin 3 → ℝ) ∈ sphere 0 1 := by
    simpa only [frontier_closedBall _ one_ne_zero] using heb x
  have hecopy := he
  obtain ⟨u, hu, heu⟩ := hecopy
  obtain ⟨v, hv, hev⟩ := he.symm
  have hum : MapsTo u C (closedBall (0 : Fin 3 → ℝ) 1) := by
    intro x hx
    rw [← heu ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hvm : MapsTo v (closedBall (0 : Fin 3 → ℝ) 1) C := by
    intro x hx
    rw [← hev ⟨x, hx⟩]
    exact (e.symm ⟨x, hx⟩).property
  have hvu : LeftInvOn v u C := by
    intro x hx
    rw [← heu ⟨x, hx⟩, ← hev, e.symm_apply_apply]
  have huv : LeftInvOn u v (closedBall (0 : Fin 3 → ℝ) 1) := by
    intro x hx
    rw [← hev ⟨x, hx⟩, ← heu, e.apply_symm_apply]
  have hub (x : E) (hx : x ∈ C) : x ∈ S ↔ u x ∈ sphere (0 : Fin 3 → ℝ) 1 := by
    rw [← heu ⟨x, hx⟩]
    exact heb' ⟨x, hx⟩
  have hvb (x : Fin 3 → ℝ) (hx : x ∈ closedBall (0 : Fin 3 → ℝ) 1) :
      v x ∈ S ↔ x ∈ sphere (0 : Fin 3 → ℝ) 1 := by
    rw [hub _ (hvm hx), huv hx]
  have hJC : J.space ⊆ C := hJS.trans hC.1
  obtain ⟨K, hK, hKJ, huK⟩ := hu.restrict J hJ hJC
  have huKi : InjOn u K.space := hvu.injOn.mono (hKJ.subset.trans hJC)
  let L := huK.embeddedImage huKi
  have hL : L.faces.Finite := huK.embeddedImage_finite huKi hK
  have hLs : L.space = u '' J.space := by
    rw [huK.embeddedImage_space huKi, hKJ]
  have hLS : L.space ⊆ sphere (0 : Fin 3 → ℝ) 1 := by
    rw [hLs]
    rintro _ ⟨x, hx, rfl⟩
    exact (hub x (hJC hx)).mp (hJS hx)
  obtain ⟨p, hp, hpi, hpm, hpfix, hpboundary⟩ :=
    PoincareConjecture.M76.exists_finitePL_cube_push_fixing_subpolyhedron L hL hLS
  let f : E → E := v ∘ p ∘ u
  have hfPL : FinitePiecewiseAffineOn f C :=
    hv.comp (hp.comp hu hum) (fun x hx => hpm (hum hx))
  refine ⟨f, hfPL, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hvu.injOn hx hy (hpi (hum hx) (hum hy)
      (huv.injOn (hpm (hum hx)) (hpm (hum hy)) hxy))
  · intro x hx
    exact hvm (hpm (hum hx))
  · intro x hx
    have hux : u x ∈ L.space := hLs.symm ▸ mem_image_of_mem u hx
    change v (p (u x)) = x
    rw [hpfix hux]
    exact hvu (hJC hx)
  · intro x hx
    change v (p (u x)) ∈ S ↔ x ∈ J.space
    rw [hvb _ (hpm (hum hx)), hpboundary _ (hum hx), hLs]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact hvu.injOn (hJC hy) hx hxy ▸ hy
    · exact fun h => mem_image_of_mem u h

end Set
