import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Reattachment.CocoreInnermostCrossings
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Collars.CircleSphereScene
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineLevelComplex

/-! # A circle tube from the actual regular cocore disk

The same innermost polygon constructs the original sphere parameter cut and
both complete sheet coordinates. The periodic tube, its closing map, and
its exact cocore and sphere incidences are derived from those coordinates.
-/

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareMT.M76
open Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem ChartwisePLSphere.exists_cocore_innermost_circle_tube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hJcv : Convex ℝ J.space)
    (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      (H x).2 ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅) ∨
      ∃ (n : ℕ) (L : Polygon V3 (n + 3)) (D U : Set V3) (k : ℕ) (sigma : P3 → V3),
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        IsFinitePLBallPair P2 D (L.boundary ℝ) ∧
        D ⊆ interior J.space ∩ {x | (H x).2 = t} ∧
        D ∩ Q '' (S ∩ Q.source) = L.boundary ℝ ∧
        IsOpen U ∧ D ⊆ U ∧ U ⊆ interior J.space ∧
        (∀ x ∈ U, x ∈ L.boundary ℝ ↔ Q.symm x ∈ S ∧ (H x).2 = t) ∧
        FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)) ∧
        MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3)) U ∧
        L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3))) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3),
          (H (sigma x)).2 = t ↔ x.1 ∈ signedTubeSheet 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3),
          Q.symm (sigma x) ∈ S ↔ x.1 ∈ signedTubeSheet 1) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k + 3),
          sigma x ∈ L.boundary ℝ ↔ x.1 = (0,0)) ∧
        (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3) = L.boundary ℝ ∧
        ∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          ∀ y ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          sigma x = sigma y ↔ x.1 = y.1 ∧
            (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = k+3) ∨ (y.2 = 0 ∧ x.2 = k+3)) := by
  obtain ⟨t,ht,hempty | ⟨n,L,D,hLi,hL,hD,hDsub,hcontact,_,U,hU,hDU,hUJ,hisolate,hcross⟩⟩ :=
    s.exists_cocore_innermost_disk_with_crossings Q hQ J hJ hJQ hJcv H hab hband
  · exact ⟨t,ht,Or.inl hempty⟩
  · obtain ⟨M,hM,hMs,_,hMlocal⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
    let A : V3 →ᴬ[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
    obtain ⟨T,hT,hTs⟩ := J.exists_finite_affineLevel_complex hJ A.toAffineMap t
    have hTlocal (x : V3) (hx : x ∈ interior J.space) : x ∈ T.space ↔ (H x).2 = t := by
      rw [hTs]
      exact ⟨fun h => h.2,fun h => ⟨interior_subset hx,h⟩⟩
    have hLP : L.boundary ℝ ⊆ M.space := by
      intro x hx
      rw [hMs]
      exact ⟨(hcontact.symm.subset hx).2,interior_subset (hDsub (hD.1 hx)).1⟩
    have hw := L.vertex_mem_boundary (0 : Fin (n+3))
    obtain ⟨B,hwB,hBJ,hBw,hB,hBi,hBS,hBA⟩ := hcross (L 0) hw univ isOpen_univ (mem_univ _)
    have hBM (x : V3) (hx : x ∈ B.source) : x ∈ M.space ↔ (B x).2 = 0 :=
      (hMlocal x (interior_subset (hBJ hx).2)).symm.trans (hBS x hx)
    have hBL (x : V3) (hx : x ∈ L.boundary ℝ ∩ B.source) : (B x).1.1 = 0 := by
      rw [← hBA x hx.2,(hDsub (hD.1 hx.1)).2,sub_self]
    obtain ⟨g,m,N,d0,d1,_,_,_,hNi,hN,hNb,hd0,_,hdunion,_,_,_,_,_,_,hgval⟩ :=
      s.exists_parameter_circle_cut Q hQ J M hJ hJQ hM hMs L hL hLi hLP B hwB hBw hBM hBL
    have hd0S : d0 ⊆ sphere (0 : V3) 1 := subset_union_left.trans hdunion.subset
    have hrimage : s.map '' N.boundary ℝ = Q.symm '' L.boundary ℝ := by
      rw [hNb,image_image]
      exact image_congr hgval
    let G : V3 →ᴬ[ℝ] P2 :=
      (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
    let E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
    let fT : V3 →ᴬ[ℝ] V2 := E.toContinuousLinearMap.toContinuousAffineMap.comp G
    have hfTi : InjOn fT T.space := by
      intro x hx y hy hxy
      apply H.injective
      apply Prod.ext
      · exact E.injective hxy
      · exact (hTs.subset hx).2.trans (hTs.subset hy).2.symm
    have hOQ : U ⊆ Q.target := hUJ.trans (interior_subset.trans hJQ)
    have hLM : ∀ x ∈ U, Q.symm x ∈ S ↔ x ∈ M.space :=
      fun x hx => hMlocal x (interior_subset (hUJ hx))
    have hiso : ∀ x ∈ U, x ∈ L.boundary ℝ ↔ x ∈ T.space ∧ x ∈ M.space := by
      intro x hx
      rw [hisolate x hx,hTlocal x (hUJ hx),← hLM x hx,and_comm]
    have hcharts : ∀ w ∈ L.boundary ℝ, ∀ V : Set V3, IsOpen V → w ∈ V →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T.space ↔ (B x).1.1 = 0 := by
      intro w hw V hV hwV
      obtain ⟨B,hwB,hBV,hBw,hB,hBi,hBS,hBA⟩ := hcross w hw V hV hwV
      refine ⟨B,hwB,fun _ hx => (hBV hx).1,hBw,hB,hBi,?_,?_⟩
      · intro x hx
        exact (hMlocal x (interior_subset (hBV hx).2)).symm.trans (hBS x hx)
      · intro x hx
        rw [hTlocal x (hBV hx).2,← sub_eq_zero, hBA x hx]
    obtain ⟨k,sigma,hSigma,hMap,hInt,hPlane,hSphere,hAxis,hImage,hFib⟩ :=
      s.exists_planar_circle_tube Q hQ T M hT fT hfTi L hL hLi N hN hNi hd0 hd0S
        hrimage hU (hD.1.trans hDU) hOQ hLM hiso hcharts
    refine ⟨t,ht,Or.inr ⟨n,L,D,U,k,sigma,hLi,hL,hD,hDsub,hcontact,hU,hDU,hUJ,
      hisolate,hSigma,hMap,hInt,?_,?_,?_,hImage,?_⟩⟩
    · intro x hx
      exact (hTlocal (sigma x) (hUJ (hMap hx))).symm.trans (hPlane ⟨x,hx⟩)
    · exact fun x hx => hSphere ⟨x,hx⟩
    · exact fun x hx => hAxis ⟨x,hx⟩
    · exact fun x hx y hy => hFib ⟨x,hx⟩ ⟨y,hy⟩

end PoincareMT.M76
