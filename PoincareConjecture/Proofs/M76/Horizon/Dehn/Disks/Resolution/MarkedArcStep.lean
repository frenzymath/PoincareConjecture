import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.NormalizedTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.TubeRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OrdinaryCounts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.MarkedFrontierNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalTubeResolutionStep

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn
open PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

theorem OrdinaryDoubleCurveModel.exists_marked_arc_resolution
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R F : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    {base : F} {J : Subgroup (FundamentalGroup F base)} [J.Normal]
    (rim : C(Q2, F)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (houtside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (hcount : 0 < doubleBoundaryComponentCount f D2 Q2) :
    ∃ (g : V2 → X) (rim' : C(Q2, F)) (basepath' : Path base (rim' squareRimBase)),
      PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧
      (∀ x : Q2, g x = (rim' x : X)) ∧
      (∀ x ∈ D2, g x ∈ F ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      basepath'.whiskeredLoopClass (squareRimLoop.map rim'.continuous) ∉ J ∧
      doubleBoundaryComponentCount g D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  classical
  have hmark : MapsTo f Q2 F := by
    intro x hx
    rw [hboundary ⟨x, hx⟩]
    exact (rim ⟨x, hx⟩).property
  have hfF (x : V2) (hx : x ∈ D2) : f x ∈ F ↔ x ∈ Q2 :=
    ⟨fun h ↦ (hfront x hx).mp (hF h), fun h ↦ hmark h⟩
  obtain ⟨O, hO, hfO, hOF⟩ := exists_open_neighborhood_of_proper_marked_map
    hF hFopen hin hfront hmark
  obtain ⟨i, hball⟩ := old.exists_interval_of_boundary_count_pos hcount
  obtain ⟨D, hD⟩ := old.exists_normalized_interval_tube hf he i hball hin hfront
  let _ : ∀ j, Fintype (D.marks j).faces := fun j ↦ (D.marks_full j).2.1.fintype
  obtain ⟨a, b, sigma, τ, ha, hb, hbval, hτeq, hsigma, hsigmai, _, hsigmaK,
    hsigmaaxis, hsigmasheet, _, hτPL, _, hτR, _, hτaxis, _, _, hτfront, _, _, _⟩ := hD
  have haxisO (t : I01) : τ ((0, 0), t) ∈ O := by
    rw [hτaxis]
    exact hfO (old.piece_subset_double i (a t).property).1
  obtain ⟨ε, hε, hε1, hεO⟩ := exists_tube_transverse_contraction_into_open
    hτPL.continuousOn hO haxisO
  let sigma' := sigma ∘ tubeTransverseContraction ε
  have hc := tubeTransverseContraction_mapsTo hε.le hε1
  have hsigma' : FinitePiecewiseAffineOn sigma' tube :=
    contracted_tube_finitePL hsigma hε.le hε1
  have hsigma'i : InjOn sigma' tube := by
    intro x hx y hy hxy
    exact tubeTransverseContraction_injective hε.ne' (hsigmai (hc hx) (hc hy) hxy)
  have hsigma'K : MapsTo sigma' tube D.complex.space := fun z hz ↦ hsigmaK (hc hz)
  have hsheet (j : Fin 2) (z : (ℝ × ℝ) × ℝ) (hz : z ∈ tube) :
      sigma' z ∈ (D.marks (.inr j.castSucc)).space ↔
        z.1.2 = if j = 0 then z.1.1 else -z.1.1 :=
    (hsigmasheet j _ (hc hz)).trans (tubeTransverseContraction_diagonal_iff hε.ne' j z)
  have hphys (z : (ℝ × ℝ) × ℝ) :
      (D.inverse (sigma' z) : X) = (τ ∘ tubeTransverseContraction ε) z := by
    rw [hτeq]
    rfl
  have hphysR : MapsTo (fun z ↦ (D.inverse (sigma' z) : X)) tube R := by
    intro z hz
    change (D.inverse (sigma' z) : X) ∈ R
    rw [hphys]
    exact hτR (hc hz)
  have hphysfront (z : (ℝ × ℝ) × ℝ) (hz : z ∈ tube) :
      (D.inverse (sigma' z) : X) ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 := by
    rw [hphys]
    exact hτfront _ (hc hz)
  have hphysF (z : (ℝ × ℝ) × ℝ) (hz : z ∈ tube) :
      (D.inverse (sigma' z) : X) ∈ F ↔ z.2 = 0 ∨ z.2 = 1 := by
    rw [← hphysfront z hz, ← hOF]
    exact and_iff_right (by rw [hphys]; exact hεO hz)
  let selected : Fin 2 → old.Index := fun j ↦ Fin.cases i (fun _ ↦ old.mate i) j
  let d := old.partner.restrictSubsets (old.piece_subset_double i)
    (old.piece_subset_double (old.mate i)) (old.partner_component_iff i)
  let alpha : ∀ j : Fin 2, I01 ≃ₜ old.pieces (selected j) :=
    fun j ↦ Fin.cases a (fun _ ↦ a.trans d) j
  have haxis (j : Fin 2) (t : I01) : sigma' ((0, 0), t) = D.graph (f (alpha j t)) := by
    change sigma (tubeTransverseContraction ε ((0, 0), t)) = _
    rw [tubeTransverseContraction_axis, hsigmaaxis, hbval]
    fin_cases j
    · rfl
    · exact congrArg D.graph (old.partner_value
        ⟨a t, old.piece_subset_double i (a t).property⟩).symm
  have hinj (j : Fin 2) : InjOn f (D.source j.castSucc).space := by
    have hem : IsEmbedding (fun x : (D.source j.castSucc).space ↦ f x) := by
      fin_cases j
      · exact D.left_embedding
      · exact D.right_embedding
    intro x hx y hy hxy
    exact congrArg Subtype.val (hem.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hAP (j : Fin 2) : old.pieces (selected j) ⊆ (D.source j.castSucc).space := by
    fin_cases j
    · exact D.left_contains
    · exact D.right_contains
  exact exists_original_model_arc_resolution e he.compatible D.core D.complex
    D.graph D.homeomorph D.inverse D.homeomorph_value D.inverse_value D.inverse_PL
    D.graph_separates (fun j : Fin 2 ↦ D.source j.castSucc)
    (fun j : Fin 2 ↦ D.clips j.castSucc) (fun j : Fin 2 ↦ D.marks (.inr j.castSucc)) f
    hinj (fun j ↦ (D.clips_data j.castSucc).2.1)
    (fun j ↦ (D.clips_data j.castSucc).2.2.1)
    (fun j ↦ (D.clips_data j.castSucc).2.2.2)
    (fun j ↦ (D.marks_full (.inr j.castSucc)).1)
    (fun j ↦ D.source_subset j.castSucc) D.disjoint
    (fun x hx ↦ D.full_preimage x hx.1 (D.core_subset hx.2))
    sigma' hsigma' hsigma'i hsigma'K hsheet old selected alpha hAP haxis hf
    rim hboundary basepath houtside hfF hphysF hin hphysR hfront hphysfront

end PoincareConjecture.M76.Dehn
