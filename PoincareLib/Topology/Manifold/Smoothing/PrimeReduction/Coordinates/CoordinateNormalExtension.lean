import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Maps.ActualWidthNormalExtension
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.BallSupportedAmbientExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages

/-!
# The actual affine normal-coordinate motion

Transport the full compact normal extension through the original affine
coordinates. Its complete boundary is fixed, so the same map extends
over the original coordinate ambient with PL regularity at its frontier.
See PrimeReduction023 sections1--3 and Hudson pp.15--19.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

/-- The original affine coordinates carry a rim-fixed central disk
map to an ambient PL homeomorphism at the actual width. Every point
off the compact normal ball interior stays fixed. See PrimeReduction023. -/
theorem exists_coordinate_normal_extension
    (T : P3 ≃ᴬ[ℝ] V3)
    {D rim : Set (ℝ × ℝ)} (hD : IsFinitePLBallPair (ℝ × ℝ) D rim)
    (e : D ≃ₜ D) (he : e.IsFinitePL)
    (hfix : ∀ x : D, (x : ℝ × ℝ) ∈ rim → e x = x)
    {r : ℝ} (hr : 0 < r) :
    ∃ G : V3 ≃ₜ V3,
      G.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 ∧
      (∀ x : D, G (T ((x : ℝ × ℝ), 0)) = T ((e x : ℝ × ℝ), 0)) ∧
      (∀ y ∉ interior (T '' (D ×ˢ Icc (-r) r)), G y = y) ∧
      ∀ (K : SimplicialComplex ℝ V3), K.faces.Finite →
        FinitePiecewiseAffineOn (G : V3 → V3) K.space := by
  obtain ⟨H, hH, hHzero, hHfix, _⟩ :=
    hD.exists_actual_width_normal_extension e he hfix hr
  let S := D ×ˢ Icc (-r) r
  let bd := (rim ×ˢ Icc (-r) r) ∪ (D ×ˢ {-r, r})
  have hS : IsFinitePLBallPair P3 S bd :=
    hD.prod (isFinitePLBallPair_Icc (show -r < r by linarith))
  have hC := hS.affine_image T.toContinuousAffineMap T.injective.injOn
  have hScopy := hS
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hScopy
  have hT : FinitePiecewiseAffineOn (T : P3 → V3) S :=
    ⟨K, hK, hKs, K.affineOnFaces_affine T.toContinuousAffineMap⟩
  obtain ⟨J, hJ, hJval⟩ := hT.exists_homeomorph_image T.injective.injOn
  have hJinv (x : T '' S) : (J.symm x : P3) = T.symm x := by
    apply T.injective
    rw [T.apply_symm_apply]
    have h := hJval (J.symm x)
    rw [J.apply_symm_apply] at h
    exact h.symm
  let P := J.symm.trans (H.trans J)
  have hP : P.IsFinitePL := hJ.symm.trans (hH.trans hJ)
  have hPfix (x : T '' S) (hx : (x : V3) ∈ T '' bd) : P x = x := by
    have hy : (J.symm x : P3) ∈ bd := by
      obtain ⟨y, hy, hxy⟩ := hx
      rw [hJinv, ← hxy, T.symm_apply_apply]
      exact hy
    have hboundary : (J.symm x : P3).1 ∈ rim ∨
        (J.symm x : P3).2 = -r ∨ (J.symm x : P3).2 = r := by
      rcases hy with hy | hy
      · exact Or.inl hy.1
      · exact Or.inr (by simpa only [mem_insert_iff, mem_singleton_iff] using hy.2)
    change J (H (J.symm x)) = x
    rw [hHfix _ hboundary, J.apply_symm_apply]
  obtain ⟨G, hGC, hGout, hGfinite, hGPL⟩ :=
    hC.exists_supported_ambient_extension (by simp [Module.finrank_prod]) P hP hPfix
  refine ⟨G, hGPL, ?_, hGout, hGfinite⟩
  intro x
  let z : S := ⟨((x : ℝ × ℝ), 0), x.property, by linarith, hr.le⟩
  let y : T '' S := ⟨T z, z, z.property, rfl⟩
  have hy : J.symm y = z := by
    apply Subtype.ext
    rw [hJinv]
    exact T.symm_apply_apply z
  have hval : (P y : V3) = T ((e x : ℝ × ℝ), 0) := by
    change (J (H (J.symm y)) : V3) = _
    rw [hJval, hy]
    change T (H z : P3) = _
    rw [hHzero x]
  exact (hGC y).trans hval

end PoincareMT.M76
