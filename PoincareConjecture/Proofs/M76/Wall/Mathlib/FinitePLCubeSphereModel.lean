import PoincareConjecture.Proofs.M76.Triangulation.StandardFinitePLSphereModel











set_option autoImplicit false

open Set Metric Geometry

namespace Homeomorph




theorem IsFinitePL.exists_unit_cube_sphere_model
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set E} {C : Set F}
    {e : S ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3) :
    ∃ b : S ≃ₜ sphere (0 : Fin 3 → ℝ) 1, b.IsFinitePL := by
  let : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (E := F) (x := (0 : F))).mpr
    (show (0 : ℝ) ≤ 1 from zero_le_one)
  obtain ⟨_, eunit, _⟩ := hC.exists_compatible_unitBall_models hcv hne
  let pC : frontier C := eunit.symm ⟨p, hp⟩
  have hecopy := he.symm
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hecopy
  let c : F ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hdim])
  obtain ⟨b, hb, _⟩ := K.exists_finitePL_convex_frontier_cube_pole
    hK hC hcv hne hKs c pC
  have htarget : frontier (closedBall (0 : Fin 3 → ℝ) 1) =
      sphere (0 : Fin 3 → ℝ) 1 := frontier_closedBall _ one_ne_zero
  let d := (e.trans b).trans (Homeomorph.setCongr htarget)
  obtain ⟨f, hf, hfeq⟩ := he.trans hb
  exact ⟨d, f, hf, fun x => hfeq x⟩

end Homeomorph
