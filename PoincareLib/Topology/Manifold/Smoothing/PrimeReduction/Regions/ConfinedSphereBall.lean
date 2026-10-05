import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonAlexanderConsequences
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionBallInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages

/-!
# A sphere filling inside a prescribed finite PL ball

The actual chart of the containing ball transports the sphere into its
convex model. Alexander's constructed bounded region lies inside that
model; its pullback is therefore confined to the prescribed ball.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76

local notation "C3" => ((ℝ × ℝ) × ℝ)

/-- Every actual finite PL sphere strictly inside a finite PL three-ball
bounds a finite PL ball strictly inside that same ball. The containing
ball's chart and the filling are constructed, with no exterior
connectedness or region-ball supplier. -/
theorem exists_confined_finitePL_sphere_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = 3)
    {S B b : Set E} {D : Set F} (e : S ≃ₜ frontier D) (he : e.IsFinitePL)
    (hD : IsCompact D) (hDcv : Convex ℝ D) (hDne : (interior D).Nonempty)
    (hdimD : Module.finrank ℝ F = 3)
    (hB : IsFinitePLBallPair C3 B b) (hSB : S ⊆ interior B) :
    ∃ R : Set E, IsFinitePLBallPair C3 R S ∧ R ⊆ interior B ∧ frontier R = S := by
  classical
  have hdimB : Module.finrank ℝ C3 = Module.finrank ℝ E := by simp [hdim]
  have hBi := hB.interior_eq_sdiff_of_finrank_eq hdimB
  obtain ⟨_,C,hC,hCcv,hCne,H,hH,hHb⟩ := hB
  obtain ⟨f,hf,hfval⟩ := hH
  obtain ⟨g,hg,hgval⟩ := (show H.IsFinitePL from ⟨f,hf,hfval⟩).symm
  have hfC (x : E) (hx : x ∈ B) : f x ∈ C := by
    rw [←hfval ⟨x,hx⟩]
    exact (H ⟨x,hx⟩).property
  have hgB (x : C3) (hx : x ∈ C) : g x ∈ B := by
    rw [←hgval ⟨x,hx⟩]
    exact (H.symm ⟨x,hx⟩).property
  have hgf (x : E) (hx : x ∈ B) : g (f x) = x := by
    rw [←hfval ⟨x,hx⟩,←hgval,H.symm_apply_apply]
  have hfg (x : C3) (hx : x ∈ C) : f (g x) = x := by
    rw [←hgval ⟨x,hx⟩,←hfval,H.apply_symm_apply]
  have hfi : InjOn f B := by
    intro x hx y hy h
    simpa only [hgf x hx,hgf y hy] using congrArg g h
  have hgi : InjOn g C := by
    intro x hx y hy h
    simpa only [hfg x hx,hfg y hy] using congrArg f h
  have hSsub : S ⊆ B := hSB.trans interior_subset
  have hfs : FinitePiecewiseAffineOn f S := by
    obtain ⟨_,⟨J,hJ,hJs,_⟩,_⟩ := he
    rw [←hJs]
    exact hf.restrict J hJ (hJs.subset.trans hSsub)
  obtain ⟨j,hj,_⟩ := hfs.exists_homeomorph_image (hfi.mono hSsub)
  have hSC : f '' S ⊆ interior C := by
    rintro _ ⟨x,hx,rfl⟩
    by_contra hn
    have hfr : f x ∈ frontier C := ⟨subset_closure (hfC x (hSsub hx)),hn⟩
    have hxb : x ∈ b := (hHb ⟨x,hSsub hx⟩).mpr (by rwa [hfval])
    exact ((hBi.subset (hSB hx)).2) hxb
  obtain ⟨K,hK,hKs,hAff⟩ := hg
  have hregions := (hj.symm.trans he).hasAlexanderRegionBalls
    hD hDcv hDne hdimD (by simp : Module.finrank ℝ C3 = 3)
    hC hCcv hCne hSC K hK hKs
  obtain ⟨U,_,_,_,hUC,hUB,_⟩ := hregions
  have hgC : FinitePiecewiseAffineOn g C := ⟨K,hK,hKs,hAff⟩
  have hR := hUB.image_of_subset hgC (hUC.trans interior_subset) hgi
  have hSimage : g '' (f '' S) = S := by
    apply Subset.antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      rwa [hgf x (hSsub hx)]
    · intro x hx
      exact ⟨f x,⟨x,hx,rfl⟩,hgf x (hSsub hx)⟩
  rw [hSimage] at hR
  refine ⟨g '' closure U,hR,?_,hR.frontier_eq_of_finrank_eq hdimB⟩
  rintro _ ⟨x,hx,rfl⟩
  have hxi := hUC hx
  have hxC := interior_subset hxi
  apply hBi.superset
  refine ⟨hgB x hxC,?_⟩
  intro hb
  have hfB := (hHb ⟨g x,hgB x hxC⟩).mp hb
  rw [hfval,hfg x hxC] at hfB
  exact hfB.2 hxi

end PoincareMT.M76
