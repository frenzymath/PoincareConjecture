import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.FinitePLBallCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.ControlledBoundaryPush

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finitePL_boundary_disk_push_avoiding_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B Q d r : Set E} (hB : IsFinitePLBallPair V3 B Q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d r) (hdQ : d ⊆ Q)
    (M : SimplicialComplex ℝ E) (hM : M.faces.Finite) (hMB : M.space ⊆ B)
    (hcontact : d ∩ M.space = r) :
    ∃ k : E → E, FinitePiecewiseAffineOn k d ∧ InjOn k d ∧ MapsTo k d B ∧
      EqOn k id r ∧ IsFinitePLBallPair (ℝ × ℝ) (k '' d) r ∧
      (k '' d) ∩ M.space = r ∧ (k '' d) ∩ Q = r := by
  obtain ⟨C, hC, hCi, hCmap, hbase, hfront⟩ := exists_finitePL_ball_inward_collar hB
  obtain ⟨K, _, hK, hKB, _, _⟩ := hB.exists_finite_carrier_and_rim_complexes
  obtain ⟨L, _, hL, hLd, _, _⟩ := hd.exists_finite_carrier_and_rim_complexes
  obtain ⟨J, _, hJ, hJI, _, _⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).exists_finite_carrier_and_rim_complexes
  obtain ⟨T, hT, hTs, _⟩ := L.exists_finite_triangulation_prod J hL hJ
  have hTd : T.space = d ×ˢ Icc (0 : ℝ) 1 := by simpa only [hLd, hJI] using hTs
  have hsub : d ×ˢ Icc (0 : ℝ) 1 ⊆ Q ×ˢ Icc (0 : ℝ) 1 := prod_mono hdQ subset_rfl
  have hCd : FinitePiecewiseAffineOn C (d ×ˢ Icc (0 : ℝ) 1) :=
    hTd ▸ hC.restrict T hT (hTd.subset.trans hsub)
  have hbaseM (x : E) (hx : x ∈ d) : C (x, 0) ∈ M.space ↔ x ∈ r := by
    rw [hbase x (hdQ hx), ← hcontact]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  obtain ⟨k, hk, hki, hkmap, hkr, hball, hinter, hboundary⟩ :=
    exists_controlled_finitePL_boundary_disk_push hd K M hK hM (hMB.trans hKB.symm.subset)
      C hCd (hCi.mono hsub) (fun x hx => hKB.symm.subset (hCmap (hsub hx)))
      hbaseM (fun z hz => hfront z (hsub hz))
  have hrbase : EqOn (fun x => C (x, 0)) id r := fun x hx => hbase x (hdQ (hd.1 hx))
  have hri : (fun x => C (x, 0)) '' r = r := (image_congr hrbase).trans (image_id r)
  refine ⟨k, hk, hki, fun x hx => hKB.subset (hkmap hx), hkr.trans hrbase, ?_, ?_, ?_⟩
  · exact hri ▸ hball
  · exact hinter.trans hri
  · exact hboundary.trans hri

end PoincareConjecture.M76
