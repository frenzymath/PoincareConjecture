import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreInnermostCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleSphereScene
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex








set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem ChartwisePLSphere.exists_fixed_cocore_circle_tubes_of_paired_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    {n : ℕ} (L : Polygon V3 (n+3)) (hLi : Function.Injective L)
    (hL : L.HasSimplicialEdges)
    (hLS : L.boundary ℝ ⊆ (Q '' (S ∩ Q.source) ∩ interior J.space) ∩ {x | (H x).2=t})
    {U : Set V3} (hUJ : U ⊆ interior J.space)
    (hisolate : ∀x∈U,x∈L.boundary ℝ ↔ Q.symm x∈S ∧ (H x).2=t)
    (hcross : ∀ w∈L.boundary ℝ, ∀ O : Set V3, IsOpen O → w∈O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀x∈B.source,Q.symm x∈S ↔ (B x).2=0) ∧ ∀x∈B.source,(H x).2=t ↔ (B x).1.1=0) :
    ∃ (d : Bool → Set V3) (r : Set V3),
      (∀b,IsFinitePLBallPair P2 (d b) r) ∧
      d true ∪ d false = sphere (0 : V3) 1 ∧ d true ∩ d false = r ∧
      s.map '' r = Q.symm '' L.boundary ℝ ∧
      ∀V : Set V3, IsOpen V → L.boundary ℝ ⊆ V → V ⊆ U →
        ∃ (k : ℕ) (sigma : P3 → V3),
          FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) ∧
          MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) V ∧
          L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3))) ∧
          (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            (H (sigma x)).2=t ↔ x.1∈signedTubeSheet 0) ∧
          (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            Q.symm (sigma x)∈S ↔ x.1∈signedTubeSheet 1) ∧
          (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            sigma x∈L.boundary ℝ ↔ x.1=(0,0)) ∧
          (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3)=L.boundary ℝ ∧
          ∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            ∀y∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
              sigma x=sigma y ↔ x.1=y.1 ∧
                (x.2=y.2 ∨ (x.2=0 ∧ y.2=k+3) ∨ (y.2=0 ∧ x.2=k+3)) := by
  obtain ⟨M,hM,hMs,_,hMlocal⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
  let A : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  obtain ⟨T,hT,hTs⟩ := J.exists_finite_affineLevel_complex hJ A.toAffineMap t
  have hTlocal (x : V3) (hx : x∈interior J.space) : x∈T.space ↔ (H x).2=t := by
    rw [hTs]
    exact ⟨fun h => h.2,fun h => ⟨interior_subset hx,h⟩⟩
  have hLP : L.boundary ℝ ⊆ M.space := by
    intro x hx
    rw [hMs]
    exact ⟨(hLS hx).1.1,interior_subset (hLS hx).1.2⟩
  obtain ⟨B,hwB,hBJ,hBw,hB,hBi,hBS,hBA⟩ :=
    hcross (L 0) (L.vertex_mem_boundary (0 : Fin (n+3))) univ isOpen_univ (mem_univ _)
  have hBM (x : V3) (hx : x∈B.source) : x∈M.space ↔ (B x).2=0 :=
    (hMlocal x (interior_subset (hBJ hx).2)).symm.trans (hBS x hx)
  have hBL (x : V3) (hx : x∈L.boundary ℝ ∩ B.source) : (B x).1.1=0 := by
    exact (hBA x hx.2).mp (hLS hx.1).2
  obtain ⟨g,m,N,d0,d1,_,_,_,hNi,hN,hNb,hd0,hd1,hdunion,hdinter,_,_,_,_,_,hgval⟩ :=
    s.exists_parameter_circle_cut Q hQ J M hJ hJQ hM hMs L hL hLi hLP B hwB hBw hBM hBL
  have hrimage : s.map '' N.boundary ℝ=Q.symm '' L.boundary ℝ := by
    rw [hNb,image_image]
    exact image_congr hgval
  let d : Bool → Set V3 := fun b => if b then d0 else d1
  refine ⟨d,N.boundary ℝ,(fun b => by cases b <;> assumption),hdunion,hdinter,hrimage,?_⟩
  intro V hV hLV hVU
  let G : V3 →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  let E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let fT : V3 →ᴬ[ℝ] V2 := E.toContinuousLinearMap.toContinuousAffineMap.comp G
  have hfTi : InjOn fT T.space := by
    intro x hx y hy hxy
    apply H.injective
    exact Prod.ext (E.injective hxy) ((hTs.subset hx).2.trans (hTs.subset hy).2.symm)
  have hVJ : V ⊆ interior J.space := hVU.trans hUJ
  have hLM : ∀x∈V,Q.symm x∈S ↔ x∈M.space :=
    fun x hx => hMlocal x (interior_subset (hVJ hx))
  have hiso : ∀x∈V,x∈L.boundary ℝ ↔ x∈T.space ∧ x∈M.space := by
    intro x hx
    rw [hisolate x (hVU hx),hTlocal x (hVJ hx),←hLM x hx,and_comm]
  have hcharts : ∀w∈L.boundary ℝ,∀O : Set V3,IsOpen O → w∈O →
      ∃B : OpenPartialHomeomorph V3 P3,
        w∈B.source ∧ B.source⊆O ∧ B w=0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀x∈B.source,x∈M.space ↔ (B x).2=0) ∧ ∀x∈B.source,x∈T.space ↔ (B x).1.1=0 := by
    intro w hw O hO hwO
    obtain ⟨B,hwB,hBO,hBw,hB,hBi,hBS,hBA⟩ := hcross w hw O hO hwO
    refine ⟨B,hwB,fun _ hx => (hBO hx).1,hBw,hB,hBi,?_,?_⟩
    · exact fun x hx => (hMlocal x (interior_subset (hBO hx).2)).symm.trans (hBS x hx)
    · intro x hx
      exact (hTlocal x (hBO hx).2).trans (hBA x hx)
  obtain ⟨k,sigma,hSigma,hMap,hInt,hPlane,hSphere,hAxis,hImage,hFib⟩ :=
    s.exists_planar_circle_tube Q hQ T M hT fT hfTi L hL hLi N hN hNi hd0
      (subset_union_left.trans hdunion.subset) hrimage hV hLV
      (hVJ.trans (interior_subset.trans hJQ)) hLM hiso hcharts
  exact ⟨k,sigma,hSigma,hMap,hInt,
    (fun x hx => (hTlocal (sigma x) (hVJ (hMap hx))).symm.trans (hPlane ⟨x,hx⟩)),
    (fun x hx => hSphere ⟨x,hx⟩),(fun x hx => hAxis ⟨x,hx⟩),hImage,
    (fun x hx y hy => hFib ⟨x,hx⟩ ⟨y,hy⟩)⟩

theorem ChartwisePLSphere.exists_fixed_cocore_circle_tubes
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    {n : ℕ} (L : Polygon V3 (n+3)) (hLi : Function.Injective L)
    (hL : L.HasSimplicialEdges)
    (hLS : L.boundary ℝ ⊆ (Q '' (S ∩ Q.source) ∩ interior J.space) ∩ {x | (H x).2=t})
    {U : Set V3} (hUJ : U ⊆ interior J.space)
    (hisolate : ∀x∈U,x∈L.boundary ℝ ↔ Q.symm x∈S ∧ (H x).2=t)
    (hcross : ∀ w∈L.boundary ℝ, ∀ O : Set V3, IsOpen O → w∈O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀x∈B.source,Q.symm x∈S ↔ (B x).2=0) ∧ ∀x∈B.source,(H x).2-t=(B x).1.1) :
    ∃ (d : Bool → Set V3) (r : Set V3),
      (∀b,IsFinitePLBallPair P2 (d b) r) ∧
      d true ∪ d false = sphere (0 : V3) 1 ∧ d true ∩ d false = r ∧
      s.map '' r = Q.symm '' L.boundary ℝ ∧
      ∀V : Set V3, IsOpen V → L.boundary ℝ ⊆ V → V ⊆ U →
        ∃ (k : ℕ) (sigma : P3 → V3),
          FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) ∧
          MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) V ∧
          L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3))) ∧
          (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            (H (sigma x)).2=t ↔ x.1∈signedTubeSheet 0) ∧
          (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            Q.symm (sigma x)∈S ↔ x.1∈signedTubeSheet 1) ∧
          (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            sigma x∈L.boundary ℝ ↔ x.1=(0,0)) ∧
          (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3)=L.boundary ℝ ∧
          ∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
            ∀y∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
              sigma x=sigma y ↔ x.1=y.1 ∧
                (x.2=y.2 ∨ (x.2=0 ∧ y.2=k+3) ∨ (y.2=0 ∧ x.2=k+3)) := by
  apply s.exists_fixed_cocore_circle_tubes_of_paired_charts Q hQ J hJ hJQ H t L hLi hL hLS hUJ hisolate ?_
  intro w hw O hO hwO
  obtain ⟨B, hwB, hBO, hBw, hB, hBi, hBS, hheight⟩ := hcross w hw O hO hwO
  refine ⟨B, hwB, hBO, hBw, hB, hBi, hBS, ?_⟩
  intro x hx
  rw [← sub_eq_zero, hheight x hx]

end PoincareConjecture.M76
