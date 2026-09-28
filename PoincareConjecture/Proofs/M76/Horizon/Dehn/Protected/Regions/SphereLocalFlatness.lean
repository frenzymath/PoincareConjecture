import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSurfaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereDisks












set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q3" => sphere (0 : V3) 1




theorem exists_finitePL_sphere_pair_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) {S : Set E}
    (b : Q3 ≃ₜ S) (hb : b.IsFinitePL) {p : E} (hp : p ∈ S) :
    ∃ H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      p ∈ H.source ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧ LocallyPiecewiseAffineOn H.symm H.target ∧
      ∀ x ∈ H.source, x ∈ S ↔ (H x).2 = 0 := by
  classical
  let C := closedBall (0 : V3) 1
  let e : S ≃ₜ frontier C := b.symm.trans
    (Homeomorph.setCongr (frontier_closedBall (0 : V3) one_ne_zero).symm)
  obtain ⟨f, ⟨K, hK, hKS, hf⟩, hfb⟩ := hb.symm
  have he : e.IsFinitePL := ⟨f, ⟨K, hK, hKS, hf⟩, hfb⟩
  have hlocal (x : K.space) : ∃ d q : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ K.space ∧ (x : E) ∈ d \ q ∧
        IsOpen ((Subtype.val : K.space → E) ⁻¹' (d \ q)) := by
    obtain ⟨d, q, hd, hdS, hx, hopen⟩ :=
      he.exists_local_ball_pairs_of_convex_frontier (isCompact_closedBall _ _)
        (convex_closedBall _ _)
        ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
        (V := ℝ × ℝ) (by simp) ⟨x, hKS.subset x.property⟩
    exact ⟨d, q, hd, hdS.trans hKS.symm.subset, hx,
      hopen.preimage (Homeomorph.setCongr hKS).continuous⟩
  obtain ⟨H, hpH, hHp, _, hH, hHi, hplane⟩ :=
    HamiltonIndexOne.exists_surface_chart_of_local_ball_pairs hdim K hK hlocal (hKS.symm ▸ hp)
  exact ⟨H, hpH, hHp, hH, hHi, fun x hx => by simpa only [hKS] using hplane x hx⟩



theorem nonempty_locallyFlat_finitePL_sphere {S : Set V3}
    (b : Q3 ≃ₜ S) (hb : b.IsFinitePL) : Nonempty (LocallyFlatTopologicalSphere S) := by
  let q : ((ℝ × ℝ) × ℝ) ≃L[ℝ] V3 :=
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans
        ((ContinuousLinearEquiv.prodComm ℝ V2 ℝ).trans
          (Fin.consEquivL ℝ (fun _ : Fin 3 => ℝ)))
  refine ⟨⟨b, ?_⟩⟩
  intro p hp
  obtain ⟨H, hpH, _, _, _, hplane⟩ := exists_finitePL_sphere_pair_chart (by simp) b hb hp
  let B := H.transHomeomorph q.toHomeomorph
  refine ⟨B, hpH, ?_⟩
  intro x hx
  exact hplane x hx

end PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)



noncomputable def image {S : Set V3} (s : LocallyFlatTopologicalSphere S)
    (c : OpenPartialHomeomorph V3 V3) (hsource : S ⊆ c.source) :
    LocallyFlatTopologicalSphere (c '' S) where
  parametrization := s.parametrization.trans (c.homeomorphOfImageSubsetSource hsource rfl)
  flatten := by
    rintro p ⟨z, hz, rfl⟩
    obtain ⟨B, hzB, hplane⟩ := s.flatten z hz
    let D := c.symm.trans B
    refine ⟨D, ⟨c.mapsTo (hsource hz), ?_⟩, ?_⟩
    · change c.symm (c z) ∈ B.source
      rwa [c.left_inv (hsource hz)]
    · intro x hx
      have hmem : x ∈ c '' S ↔ c.symm x ∈ S := by
        constructor
        · rintro ⟨y, hy, rfl⟩
          rwa [c.left_inv (hsource hy)]
        · intro hy
          exact ⟨c.symm x, hy, c.right_inv hx.1⟩
      exact hmem.trans (hplane (c.symm x) hx.2)



theorem nonempty_inverse_chart_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set V3} (s : LocallyFlatTopologicalSphere S)
    (h : OpenPartialHomeomorph E V3) (a : E ≃L[ℝ] V3) (htarget : S ⊆ h.target) :
    Nonempty (LocallyFlatTopologicalSphere (a '' (h.symm '' S))) := by
  let c := h.symm.transHomeomorph a.toHomeomorph
  have hsource : S ⊆ c.source := htarget
  have himage : c '' S = a '' (h.symm '' S) := (image_image a h.symm S).symm
  exact ⟨himage ▸ s.image c hsource⟩

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
