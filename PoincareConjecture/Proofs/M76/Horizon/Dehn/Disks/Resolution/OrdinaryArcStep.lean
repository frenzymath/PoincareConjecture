import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalSelectedResolutionStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OriginalOrdinaryResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.MarkedRimFromTrace









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1




theorem exists_ordinary_arc_resolution
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {f : V2 → X} {Z R : Set X} {base : Z}
    {H : Subgroup (FundamentalGroup Z base)} [H.Normal]
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (rim : C(Q2, Z)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (houtside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ H)
    (c : Bool → P2 → V2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q2 ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hfR : MapsTo f D2 R) (hτR : MapsTo τ tube R)
    (hffrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (hτfrontier : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (a b : old.Index) (ha : old.pieces a = c false '' arm 0)
    (hb : old.pieces b = c true '' arm 0) :
    ∃ (g : V2 → X) (rim' : C(Q2, Z)) (basepath' : Path base (rim' squareRimBase)),
      PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧
      (∀ x : Q2, g x = (rim' x : X)) ∧
      (∀ x ∈ D2, g x ∈ Z ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      basepath'.whiskeredLoopClass (squareRimLoop.map rim'.continuous) ∉ H ∧
      doubleBoundaryComponentCount g D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  let : Finite old.Index := old.finiteIndex
  obtain ⟨D, P, g, rho, hg, hproper, hrho, hout, hcount, hinterior, hgR, hgfrontier,
    _, hchoice⟩ := exists_original_selected_resolution_with_decrease e hcompat hf rim
      hboundary basepath houtside c hcPL hci hcS hcQ hdisj hτ hτi hfull h0 h1 hfZ hτZ
      hfR hτR hffrontier hτfrontier old.pieces old.mate old.partner old.cover
      old.compact old.connected old.disjoint (fun x ↦ (old.partner_value x).symm)
      (fun x ↦ Ne.symm (old.partner_free x)) old.unique_partner old.partner_component a b ha hb
  obtain ⟨rim', basepath', hboundary', hclass⟩ := exists_marked_rim_of_trace g hg.continuousOn
    (fun x hx ↦ (hproper x (sphere_subset_closedBall hx)).mpr hx) rho P.whisker hrho
  obtain ⟨hU, hV⟩ := P.nonempty_ordinary_models old hf.continuousOn hτ.continuousOn
    hcPL hci hcS hcQ hdisj hτi hfull h0 h1 hfZ a b ha hb
  refine ⟨g, rim', basepath', hg, hgR, hboundary', hproper, hgfrontier,
    hclass ▸ hout, hcount, hinterior, ?_⟩
  rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact hU
  · exact hV

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
