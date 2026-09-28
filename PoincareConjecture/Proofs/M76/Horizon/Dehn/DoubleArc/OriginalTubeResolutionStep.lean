import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalTubeSourceStrips
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Resolution.OrdinaryArcStep

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_original_model_arc_resolution
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (C : Set X) (K : SimplicialComplex ℝ E)
    (F : X → E) (H : C ≃ₜ K.space) (g : E → C)
    (hH : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (hsep : ∀ x ∈ C, ∀ y : X, F x = F y → x = y)
    (P T : Fin 2 → SimplicialComplex ℝ V2)
    (M : Fin 2 → SimplicialComplex ℝ E) (f : V2 → X)
    (hinj : ∀ i, InjOn f (P i).space)
    (hclip : ∀ i, (T i).space = (P i).space ∩ f ⁻¹' C)
    (hPL : ∀ i, FinitePiecewiseAffineOn (F ∘ f) (T i).space)
    (himage : ∀ i, (F ∘ f) '' (T i).space = (M i).space)
    (hMK : ∀ i, M i ≤ K)
    (hPD : ∀ i, (P i).space ⊆ D2)
    (hdisj : Disjoint (P 0).space (P 1).space)
    (hconfine : D2 ∩ f ⁻¹' C ⊆ (P 0).space ∪ (P 1).space)
    (tau : C3 → E) (htauPL : FinitePiecewiseAffineOn tau tube)
    (htaui : InjOn tau tube) (htauK : MapsTo tau tube K.space)
    (hsheet : ∀ i z, z ∈ tube →
      (tau z ∈ (M i).space ↔ z.1.2 = if i = 0 then z.1.1 else -z.1.1))
    {Z R : Set X} {base : Z} {J : Subgroup (FundamentalGroup Z base)} [J.Normal]
    (old : OrdinaryDoubleCurveModel e f R)
    (selected : Fin 2 → old.Index)
    (alpha : ∀ i, Icc (0 : ℝ) 1 ≃ₜ old.pieces (selected i))
    (hAP : ∀ i, old.pieces (selected i) ⊆ (P i).space)
    (haxis : ∀ i (t : Icc (0 : ℝ) 1), tau ((0, 0), t) = F (f (alpha i t)))
    (hf : PolyhedralPLInCharts e f D2)
    (rim : C(Q2, Z)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (houtside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J)
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (htauZ : ∀ z ∈ tube, (g (tau z) : X) ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hfR : MapsTo f D2 R) (htauR : MapsTo (fun z => (g (tau z) : X)) tube R)
    (hffrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (htaufrontier : ∀ z ∈ tube,
      (g (tau z) : X) ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ (f' : V2 → X) (rim' : C(Q2, Z)) (basepath' : Path base (rim' squareRimBase)),
      PolyhedralPLInCharts e f' D2 ∧ MapsTo f' D2 R ∧
      (∀ x : Q2, f' x = (rim' x : X)) ∧
      (∀ x ∈ D2, f' x ∈ Z ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, f' x ∈ frontier R ↔ x ∈ Q2) ∧
      basepath'.whiskeredLoopClass (squareRimLoop.map rim'.continuous) ∉ J ∧
      doubleBoundaryComponentCount f' D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount f' D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e f' R) := by
  obtain ⟨c, hc, hcd, hphysical, hte, hcv, hfull, _, hcenters, hproper⟩ :=
    exists_original_parameterized_tube_source_strips e C K F H g hH hg hgPL hsep
      P T M f hinj hclip hPL himage hMK hPD hdisj hconfine tau htauPL htaui htauK
      hsheet (fun i => old.pieces (selected i)) alpha hAP haxis
  have hci (i : Bool) : InjOn (c i) source := by
    intro p hp q hq he
    exact congrArg Subtype.val ((hc i).2.1.injective
      (show (fun p : source => c i p) ⟨p, hp⟩ =
        (fun p : source => c i p) ⟨q, hq⟩ from he))
  have hti : InjOn (fun z => (g (tau z) : X)) tube := by
    intro z hz w hw he
    exact congrArg Subtype.val (hte.injective
      (show (fun z : tube => (g (tau z) : X)) ⟨z, hz⟩ =
        (fun z : tube => (g (tau z) : X)) ⟨w, hw⟩ from he))
  exact exists_ordinary_arc_resolution e hcompat old hf rim hboundary basepath houtside
    c (fun i => (hc i).1) hci (fun i => (hc i).2.2) (hproper Z Q2 hfZ htauZ) hcd
    hphysical hti hfull (hcv false) (hcv true) hfZ htauZ hfR htauR hffrontier
    htaufrontier (selected 0) (selected 1) (hcenters false).symm (hcenters true).symm

end PoincareConjecture.M76.Dehn
