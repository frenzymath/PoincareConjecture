import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalResolutionComponentDecrease
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalResolutionProperness

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

theorem exists_original_selected_resolution_with_decrease
    {F X ι I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [Finite I] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {f : V2 → X} {Z : Set X} {base : Z} {H : Subgroup (FundamentalGroup Z base)} [H.Normal]
    (hf : PolyhedralPLInCharts e f D2)
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
    {R : Set X} (hfR : MapsTo f D2 R) (hτR : MapsTo τ tube R)
    (hffrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (hτfrontier : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (U : I → Set V2) (mate : I → I)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hpartner : ∀ x : doubleLocusOn f D2, f x = f (partner x))
    (hne : ∀ x : doubleLocusOn f D2, (x : V2) ≠ partner x)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (partner x : V2) ∈ U (mate i))
    (a b : I) (ha : U a = c false '' arm 0) (hb : U b = c true '' arm 0) :
    ∃ (D : OriginalResolutionWordExclusionData f Z base H c τ (1 / 4))
      (P : OriginalNormalizedResolutionPairData e D) (g : V2 → X)
      (rho : Path D.E0.c D.E0.c),
      PolyhedralPLInCharts e g D2 ∧ (∀ x ∈ D2, g x ∈ Z ↔ x ∈ Q2) ∧
      (∀ t : I01, (rho t : X) = g (squareRimLoop t)) ∧
      P.whisker.whiskeredLoopClass rho ∉ H ∧
      doubleBoundaryComponentCount g D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 ∧
      MapsTo g D2 R ∧ (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
        g x = g y → g x = g z → x ≠ y → x ≠ z → y = z) ∧
      ((g = P.gU ∧ rho = P.RU) ∨ (g = P.gV ∧ rho = P.RV)) := by
  obtain ⟨D, P, g, rho, hg, hproper, hrim, hout, hchoice⟩ :=
    exists_original_selected_normalized_resolution e hcompat hf rim hboundary basepath houtside
      c hcPL hci hcS hcQ hdisj hτ h0 h1 hfZ hτZ
  have hcounts := P.component_counts_decrease hci hcS hcQ hdisj hτi hfull h0 h1 hfZ
    U mate partner hcover hcompact hconn hpairwise hpartner hne hunique hmate a b ha hb
  have hcount : doubleBoundaryComponentCount g D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hcounts.1
    · exact hcounts.2
  obtain ⟨hRU, hRV, hFU, hFV⟩ := P.region_properness hfR hτR hffrontier hτfrontier hfZ hτZ
  have hunique' := P.unique_other_points hτi hfull h0 h1 hfZ partner hunique
  have hgeometry : MapsTo g D2 R ∧ (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
        g x = g y → g x = g z → x ≠ y → x ≠ z → y = z) := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨hRU, hFU, hunique'.1⟩
    · exact ⟨hRV, hFV, hunique'.2⟩
  exact ⟨D, P, g, rho, hg, hproper, hrim, hout, hcount.1, hcount.2,
    hgeometry.1, hgeometry.2.1, hgeometry.2.2, hchoice⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
