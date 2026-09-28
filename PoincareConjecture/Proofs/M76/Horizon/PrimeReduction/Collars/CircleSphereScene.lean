import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CirclePlanarSigns
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CirclePlanarNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PairedChartRestriction









set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)



theorem ChartwisePLSphere.exists_finitePL_sheet_circle_tube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (T M : SimplicialComplex ℝ V3) (hT : T.faces.Finite)
    (fT : V3 → V2) (hfT : FinitePiecewiseAffineOn fT T.space) (hfTi : InjOn fT T.space)
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    {m : ℕ} (R : Polygon V3 (m + 3))
    (hR : R.HasSimplicialEdges) (hRi : Function.Injective R)
    {d : Set V3} (hd : IsFinitePLBallPair P2 d (R.boundary ℝ))
    (hdS : d ⊆ sphere (0 : V3) 1)
    (hrimage : s.map '' R.boundary ℝ = Q.symm '' L.boundary ℝ)
    {O : Set V3} (hO : IsOpen O) (hLO : L.boundary ℝ ⊆ O) (hOQ : O ⊆ Q.target)
    (hMlocal : ∀ x ∈ O, Q.symm x ∈ S ↔ x ∈ M.space)
    (hisolate : ∀ x ∈ O, x ∈ L.boundary ℝ ↔ x ∈ T.space ∧ x ∈ M.space)
    (hcrossings : ∀ w ∈ L.boundary ℝ, ∀ V : Set V3, IsOpen V → w ∈ V →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T.space ↔ (B x).1.1 = 0) :
    ∃ (k : ℕ) (sigma : C3 → V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)) O ∧
      L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3))) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        sigma x ∈ T.space ↔ (x : C3).1 ∈ signedTubeSheet 0) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        Q.symm (sigma x) ∈ S ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ => sigma ((0, 0), t)) '' Icc (0 : ℝ) (k + 3) = L.boundary ℝ ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        sigma x = sigma y ↔ (x : C3).1 = (y : C3).1 ∧
          ((x : C3).2 = (y : C3).2 ∨
            ((x : C3).2 = 0 ∧ (y : C3).2 = k + 3) ∨
            ((y : C3).2 = 0 ∧ (x : C3).2 = k + 3)) := by
  classical
  obtain ⟨p, A, q, F, hp, hpA, hA, hAS, hRA, hAopen, hF, hFq,
      f, g, hf, hg, hfi, hgi, hgf, hfg, hfA, hfq, hFf,
      r, P, hPi, hP, hPb, hPmem, hPint, U, hU, hrU, hSU, B, hB⟩ :=
    s.exists_circle_planar_neighborhood R hR hRi hd hdS
  let V := O ∩ (Q.target ∩ Q.symm ⁻¹' U)
  have hV : IsOpen V := hO.inter (Q.symm.isOpen_inter_preimage hU)
  have hLV : L.boundary ℝ ⊆ V := by
    intro x hx
    exact ⟨hLO hx, hOQ (hLO hx), hrU (hrimage.symm.subset ⟨x, hx, rfl⟩)⟩
  obtain ⟨J, hJ, hLJ, hJV⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed L.isCompact_boundary hV hLV
  have hJQ : J.space ⊆ Q.target := fun _ hx => (hJV hx).2.1
  obtain ⟨Ps, hPs, hPseq, _, hPsLocal⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
  obtain ⟨v, hv, hvS, hvi, hvright, hvleft, hvimage⟩ :=
    s.exists_finite_clipped_parameter Q hQ J Ps hJ hJQ hPs hPseq
  have hvA : MapsTo v Ps.space A := by
    intro x hx
    have hxJ := (hPseq.subset hx).2
    have hxU : Q.symm x ∈ U := (hJV hxJ).2.2
    have hxS : Q.symm x ∈ S := (hPsLocal x hxJ).mpr hx
    obtain ⟨y, hy, hyx⟩ := hSU.subset ⟨hxS, hxU⟩
    have hvy : v x = y := by
      have hmap : s.map (v x) = s.map y := (hvright x hx).trans hyx.symm
      rw [s.map_eq ⟨v x, hvS hx⟩, s.map_eq ⟨y, hAS hy.1⟩] at hmap
      exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hmap))
    exact hvy ▸ hy.1
  let E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let fSphere : V3 → V2 := E ∘ f ∘ v
  have hfSphere : FinitePiecewiseAffineOn fSphere Ps.space :=
    (hf.comp hv hvA).postcomp E.toContinuousAffineEquiv.toContinuousAffineMap
  have hfSpherei : InjOn fSphere Ps.space := by
    intro x hx y hy heq
    exact hvi hx hy (hfi (hvA hx) (hvA hy) (E.injective heq))
  let marks : Fin 3 → SimplicialComplex ℝ V3 := ![T, Ps, L.simplicialComplex hL]
  have hmarks (j : Fin 3) : (marks j).faces.Finite := by
    fin_cases j
    · exact hT
    · exact hPs
    · exact L.finite_simplicialComplex_faces hL
  have hPL : (marks 2).space = L.boundary ℝ := L.simplicialComplex_space hL
  have hlocal (x : V3) (hx : x ∈ interior J.space) :
      x ∈ Ps.space ↔ x ∈ M.space :=
    (hPsLocal x (interior_subset hx)).symm.trans (hMlocal x (hJV (interior_subset hx)).1)
  have hIso (x : V3) (hx : x ∈ interior J.space) :
      x ∈ L.boundary ℝ ↔ x ∈ (marks 0).space ∧ x ∈ (marks 1).space := by
    change x ∈ L.boundary ℝ ↔ x ∈ T.space ∧ x ∈ Ps.space
    rw [hlocal x hx]
    exact hisolate x (hJV (interior_subset hx)).1
  have hcharts : ∀ x ∈ L.boundary ℝ, ∃ H : OpenPartialHomeomorph V3 V3,
      x ∈ H.source ∧ H ∈ piecewiseAffineGroupoid V3 ∧
      ∀ (j : Fin 2) y, y ∈ H.source →
        (y ∈ (marks j.castSucc).space ↔ H y j.castSucc = 0) := by
    intro x hx
    obtain ⟨B, hxB, hBJ, hBx, hB, hBi, hBM, hBT⟩ :=
      hcrossings x hx (interior J.space) isOpen_interior (hLJ hx)
    have hBPs (y : V3) (hy : y ∈ B.source) : y ∈ Ps.space ↔ (B y).2 = 0 :=
      (hlocal y (hBJ hy)).trans (hBM y hy)
    obtain ⟨H, hH, hxH, hHs, hHx, hHsheet⟩ :=
      exists_ordered_interior_crossing_chart B hB hBi hxB hBx
        (fun j : Fin 2 => (marks j.castSucc).space) hBT hBPs
    exact ⟨H, hxH, hH, hHsheet⟩
  let coords : Fin 2 → V3 → V2 := ![fT, fSphere]
  have hcoords (j : Fin 2) : FinitePiecewiseAffineOn (coords j) (marks j.castSucc).space := by
    fin_cases j
    · exact hfT
    · exact hfSphere
  have hcoordsi (j : Fin 2) : InjOn (coords j) (marks j.castSucc).space := by
    fin_cases j
    · exact hfTi
    · exact hfSpherei
  obtain ⟨k, sigma, hSigma, hSigmaJ, hInt, hSheet, hAxis, hImage, hFib⟩ :=
    exists_coordinate_identity_circle_tube marks hmarks L hL hLi hPL
      isOpen_interior hLJ hIso hcharts coords hcoords hcoordsi
  refine ⟨k, sigma, hSigma, fun x hx => (hJV (interior_subset (hSigmaJ hx))).1,
    hInt, hSheet 0, ?_, hAxis, hImage, hFib⟩
  intro x
  exact (hPsLocal (sigma x) (interior_subset (hSigmaJ x.property))).trans (hSheet 1 x)

theorem ChartwisePLSphere.exists_planar_circle_tube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (T M : SimplicialComplex ℝ V3) (hT : T.faces.Finite)
    (fT : V3 →ᴬ[ℝ] V2) (hfTi : InjOn fT T.space)
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    {m : ℕ} (R : Polygon V3 (m + 3))
    (hR : R.HasSimplicialEdges) (hRi : Function.Injective R)
    {d : Set V3} (hd : IsFinitePLBallPair P2 d (R.boundary ℝ))
    (hdS : d ⊆ sphere (0 : V3) 1)
    (hrimage : s.map '' R.boundary ℝ = Q.symm '' L.boundary ℝ)
    {O : Set V3} (hO : IsOpen O) (hLO : L.boundary ℝ ⊆ O) (hOQ : O ⊆ Q.target)
    (hMlocal : ∀ x ∈ O, Q.symm x ∈ S ↔ x ∈ M.space)
    (hisolate : ∀ x ∈ O, x ∈ L.boundary ℝ ↔ x ∈ T.space ∧ x ∈ M.space)
    (hcrossings : ∀ w ∈ L.boundary ℝ, ∀ V : Set V3, IsOpen V → w ∈ V →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T.space ↔ (B x).1.1 = 0) :
    ∃ (k : ℕ) (sigma : C3 → V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)) O ∧
      L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3))) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        sigma x ∈ T.space ↔ (x : C3).1 ∈ signedTubeSheet 0) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        Q.symm (sigma x) ∈ S ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ => sigma ((0, 0), t)) '' Icc (0 : ℝ) (k + 3) = L.boundary ℝ ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)),
        sigma x = sigma y ↔ (x : C3).1 = (y : C3).1 ∧
          ((x : C3).2 = (y : C3).2 ∨
            ((x : C3).2 = 0 ∧ (y : C3).2 = k + 3) ∨
            ((y : C3).2 = 0 ∧ (x : C3).2 = k + 3)) := by
  exact s.exists_finitePL_sheet_circle_tube Q hQ T M hT fT
    ((T.affineOnFaces_affine fT).finitePiecewiseAffineOn hT) hfTi L hL hLi R hR hRi
    hd hdS hrimage hO hLO hOQ hMlocal hisolate hcrossings

end PoincareConjecture.M76
