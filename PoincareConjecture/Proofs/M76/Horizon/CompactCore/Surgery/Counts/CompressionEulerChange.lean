import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.RetainedFrontierModel
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionAnnulusEulerCount
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionCapsEulerCount
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_compression_graph_euler_change
    {E Eold X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
    [FiniteDimensional ℝ Eold] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (phi : X → E) (hphi : Continuous phi) (hinj : InjOn phi (F ∪ P.closedStrip))
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hFK : phi '' F ⊆ K.space) (hBK : phi '' P.closedStrip ⊆ K.space)
    {n : ℕ} (Old : Fin n → SimplicialComplex ℝ Eold) (g : Eold → X)
    (hOld : ∀ i, (Old i).faces.Finite)
    (hg : ∀ i, PolyhedralPLInCharts e g (Old i).space)
    (hOldF : (⋃ i, g '' (Old i).space) = F) :
    ∃ Aold Anew : SimplicialComplex ℝ E,
      Aold.faces.Finite ∧ Anew.faces.Finite ∧
      Aold.space = phi '' F ∧
      Anew.space = phi '' ((F \ P.openStrip) ∪ P.endDisks) ∧
      Anew.surfaceEulerCount = Aold.surfaceEulerCount + 2 := by
  obtain ⟨R, Aold, Anew, Retained, Annulus, CapUnion, Caps, Rims,
    hR, _, hAR, hNR, hRetR, hAnnR, hCapUR, hAs, hNs, _, hAnns, hCapUs,
    hAfaces, hNfaces, hGlue, hCapFaces, hCaps, _, _⟩ :=
    P.exists_retained_frontier_graph_model hF hcut hsmall hlateral phi hphi hinj hphiPL
      K hK hFK hBK Old g hOld hg hOldF
  have hann : Annulus.surfaceEulerCount = 0 := by
    apply P.annulus_image_surfaceEulerCount phi hphiPL hinj subset_union_right
      Annulus (hR.subset hAnnR)
    rw [hAnns, P.frontier_mark_inter_closedStrip hcut hsmall]
  have hcaps : CapUnion.surfaceEulerCount = 2 := by
    apply P.caps_image_surfaceEulerCount phi hphiPL hinj subset_union_right
      Caps CapUnion (fun b => hR.subset (hCaps b).1) (fun b => (hCaps b).2)
    · intro b s hs
      change s ∈ CapUnion.faces
      rw [hCapFaces]
      cases b with
      | false => exact Or.inl hs
      | true => exact Or.inr hs
    · rw [hCapUs, (hCaps false).2, (hCaps true).2, ← image_union,
        P.endDisks_eq_capDisks]
  have hold := Retained.surfaceEulerCount_union_add_inter Annulus Aold
    (hR.subset hRetR) (hR.subset hAnnR) hAfaces
  have hnew := Retained.surfaceEulerCount_union_add_inter CapUnion Anew
    (hR.subset hRetR) (hR.subset hCapUR) hNfaces
  rw [hGlue] at hold
  exact ⟨Aold, Anew, hR.subset hAR, hR.subset hNR, hAs, hNs, by omega⟩

theorem exists_original_compression_euler_change
    {Eold X ι : Type*} [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
    [FiniteDimensional ℝ Eold] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (hN : PLDomain e N) (hNc : IsCompact N) (hcontain : F ∪ P.closedStrip ⊆ N)
    {n : ℕ} (Old : Fin n → SimplicialComplex ℝ Eold) (g : Eold → X)
    (hOld : ∀ i, (Old i).faces.Finite)
    (hg : ∀ i, PolyhedralPLInCharts e g (Old i).space)
    (hOldF : (⋃ i, g '' (Old i).space) = F) :
    ∃ (s : Finset N) (phi : X → (s → ℝ × V3))
      (Aold Anew : SimplicialComplex ℝ (s → ℝ × V3)),
      Continuous phi ∧ InjOn phi N ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      Aold.faces.Finite ∧ Anew.faces.Finite ∧
      Aold.space = phi '' F ∧
      Anew.space = phi '' ((F \ P.openStrip) ∪ P.endDisks) ∧
      Anew.surfaceEulerCount = Aold.surfaceEulerCount + 2 := by
  have hNne : N.Nonempty := by
    refine ⟨P.map (0, 0), hcontain (Or.inr ?_)⟩
    exact ⟨(0, 0), ⟨mem_closedBall_self zero_le_one, by norm_num⟩, rfl⟩
  obtain ⟨s, phi, K, A, H, gN, HB, hphi, hphiPL, hK, _, _, _, hKs, _, hH, _⟩ :=
    hN.exists_original_frontier_surface_model hNc hNne
  have hinj : InjOn phi N := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hFK : phi '' F ⊆ K.space := by
    rw [hKs]
    exact image_mono (subset_union_left.trans hcontain)
  have hBK : phi '' P.closedStrip ⊆ K.space := by
    rw [hKs]
    exact image_mono (subset_union_right.trans hcontain)
  obtain ⟨Aold, Anew, hcounts⟩ := P.exists_compression_graph_euler_change hF hcut hsmall
    hlateral phi hphi (hinj.mono hcontain) hphiPL K hK hFK hBK Old g hOld hg hOldF
  exact ⟨s, phi, Aold, Anew, hphi, hinj, hphiPL, hcounts⟩

end PoincareConjecture.M76.OriginalDiskProduct
