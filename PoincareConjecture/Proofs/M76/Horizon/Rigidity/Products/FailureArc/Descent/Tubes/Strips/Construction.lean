import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Models.NormalizedTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.SourceStrips
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.TubeRestriction

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "stripSource" => PolygonalCrossingResolution.source

theorem SourceDoubleComponents.exists_interval_tube_source_strips
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X}
    {S Q : Set E} {R W : Set X}
    (old : SourceDoubleComponents e f S Q R) (hf : PolyhedralPLInCharts e f S)
    (he : PLDomain e R) (i : old.Index)
    (hball : IsFinitePLBallPair ℝ (old.pieces i) (old.pieces i ∩ Q))
    (hin : MapsTo f S R) (hfront : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ Q)
    (hW : IsOpen W) (hAW : f '' old.pieces i ⊆ W) :
    ∃ (c : Bool → P2 → E) (τ : C3 → X),
      (∀ j, FinitePiecewiseAffineOn (c j) stripSource ∧
        IsEmbedding (fun p : stripSource => c j p) ∧ MapsTo (c j) stripSource S) ∧
      Disjoint (c false '' stripSource) (c true '' stripSource) ∧
      PolyhedralPLInCharts e τ tube ∧ IsEmbedding (fun z : tube => τ z) ∧
      MapsTo τ tube R ∧ MapsTo τ tube W ∧
      (∀ j p, p ∈ stripSource → f (c j p) = τ (originalStripSheet j p)) ∧
      S ∩ f ⁻¹' (τ '' tube) = c false '' stripSource ∪ c true '' stripSource ∧
      (∀ j, c j '' arm 0 = old.pieces (if j then old.mate i else i)) ∧
      (∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) ∧
      ∀ j p, p ∈ stripSource → (c j p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1) := by
  classical
  obtain ⟨D, hD⟩ := old.exists_normalized_interval_tube hf he i hball hin hfront
  let _ : ∀ j, Fintype (D.marks j).faces := fun j => (D.marks_full j).2.1.fintype
  obtain ⟨a, b, sigma, τ, _ha, _hb, hbval, hτeq, hsigma, hsigmai, _, hsigmaK,
    hsigmaaxis, hsigmasheet, _, hτPL, _, hτR, _, hτaxis, _, _, hτfront, _, _, _⟩ := hD
  have haxisW (t : I01) : τ ((0, 0), t) ∈ W := by
    rw [hτaxis]
    exact hAW ⟨a t, (a t).property, rfl⟩
  obtain ⟨ε, hε, hε1, hεW⟩ := exists_tube_transverse_contraction_into_open
    hτPL.continuousOn hW haxisW
  let sigma' := sigma ∘ tubeTransverseContraction ε
  have hc := tubeTransverseContraction_mapsTo hε.le hε1
  have hsigma' : FinitePiecewiseAffineOn sigma' tube :=
    contracted_tube_finitePL hsigma hε.le hε1
  have hsigma'i : InjOn sigma' tube := by
    intro x hx y hy hxy
    exact tubeTransverseContraction_injective hε.ne' (hsigmai (hc hx) (hc hy) hxy)
  have hsigma'K : MapsTo sigma' tube D.complex.space := fun z hz => hsigmaK (hc hz)
  have hsheet (j : Fin 2) (z : C3) (hz : z ∈ tube) :
      sigma' z ∈ (D.marks (.inr j.castSucc)).space ↔
        z.1.2 = if j = 0 then z.1.1 else -z.1.1 :=
    (hsigmasheet j _ (hc hz)).trans (tubeTransverseContraction_diagonal_iff hε.ne' j z)
  let physical : C3 → X := fun z => (D.inverse (sigma' z) : X)
  have hphys (z : C3) : physical z = (τ ∘ tubeTransverseContraction ε) z := by
    rw [hτeq]
    rfl
  have hphysR : MapsTo physical tube R := by
    intro z hz
    rw [hphys]
    exact hτR (hc hz)
  have hphysW : MapsTo physical tube W := by
    intro z hz
    rw [hphys]
    exact hεW hz
  have hphysfront (z : C3) (hz : z ∈ tube) :
      physical z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 := by
    rw [hphys]
    exact hτfront _ (hc hz)
  let selected : Fin 2 → old.Index := fun j => Fin.cases i (fun _ => old.mate i) j
  let d := old.partner.restrictSubsets (old.pieces_subset i)
    (old.pieces_subset (old.mate i)) (old.partner_component i)
  let alpha : ∀ j : Fin 2, I01 ≃ₜ old.pieces (selected j) :=
    fun j => Fin.cases a (fun _ => a.trans d) j
  have haxis (j : Fin 2) (t : I01) : sigma' ((0, 0), t) = D.graph (f (alpha j t)) := by
    change sigma (tubeTransverseContraction ε ((0, 0), t)) = _
    rw [tubeTransverseContraction_axis, hsigmaaxis, hbval]
    fin_cases j
    · rfl
    · exact congrArg D.graph (old.value ⟨a t, old.pieces_subset i (a t).property⟩).symm
  have hinj (j : Fin 2) : InjOn f (D.source j.castSucc).space := by
    have hem : IsEmbedding (fun x : (D.source j.castSucc).space => f x) := by
      fin_cases j
      · exact D.left_embedding
      · exact D.right_embedding
    intro x hx y hy hxy
    exact congrArg Subtype.val (hem.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hAP (j : Fin 2) : old.pieces (selected j) ⊆ (D.source j.castSucc).space := by
    fin_cases j
    · exact D.left_contains
    · exact D.right_contains
  obtain ⟨c, hcs, hdis, hPL, hem, hval, hfull, _haxis, hcenter, hrim⟩ :=
    exists_original_parameterized_tube_source_strips e D.core D.complex
      D.graph D.homeomorph D.inverse D.homeomorph_value D.inverse_value D.inverse_PL
      D.graph_separates (fun j : Fin 2 => D.source j.castSucc)
      (fun j : Fin 2 => D.clips j.castSucc) (fun j : Fin 2 => D.marks (.inr j.castSucc)) f
      hinj (fun j => (D.clips_data j.castSucc).2.1)
      (fun j => (D.clips_data j.castSucc).2.2.1)
      (fun j => (D.clips_data j.castSucc).2.2.2)
      (fun j => (D.marks_full (.inr j.castSucc)).1)
      (fun j => D.source_subset j.castSucc) D.disjoint
      (fun x hx => D.full_preimage x hx.1 (D.core_subset hx.2))
      sigma' hsigma' hsigma'i hsigma'K hsheet (fun j => old.pieces (selected j))
      alpha hAP haxis
  refine ⟨c, physical, hcs, hdis, hPL, hem, hphysR, hphysW, hval, hfull, ?_,
    hphysfront, hrim (frontier R) Q hfront hphysfront⟩
  intro j
  cases j
  · exact hcenter false
  · exact hcenter true

end PoincareConjecture.M76.Dehn.Annuli
