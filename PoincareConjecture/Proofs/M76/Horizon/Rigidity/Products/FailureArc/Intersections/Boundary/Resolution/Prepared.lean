import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.Enlarge
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Local

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_prepared_original_returning_arc_removal
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R O : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hO : IsOpen O)
    {T₀ Q₀ D₀ E₀ U₀ S₀ H₀ D₁ E₁ U₁ S₁ Q₁ H₁ : Set P2}
    {c₀ c₁ : P2 → P2} {f₀ f₁ : P2 → X} {τ : C3 → X}
    (hT₀ : IsFinitePLBallPair P2 T₀ Q₀)
    (hD₀ : IsFinitePLBallPair P2 D₀ (U₀ ∪ c₀ '' arm 0))
    (hE₀ : IsFinitePLBallPair P2 E₀ ((E₀ ∩ Q₀) ∪ c₀ '' arm 0))
    (hU₀ : IsFinitePLBallPair ℝ U₀ {c₀ (0, 0), c₀ (1, 0)})
    (hDU₀ : D₀ ∩ Q₀ = U₀) (hcover₀ : D₀ ∪ E₀ = T₀)
    (hcommon₀ : D₀ ∩ E₀ = c₀ '' arm 0)
    (hD₁ : IsFinitePLBallPair P2 D₁ (U₁ ∪ c₁ '' arm 0))
    (hDU₁ : D₁ ∩ Q₁ = U₁)
    (hcover₁ : S₁ ⊆ E₁ ∪ D₁) (hcommon₁ : E₁ ∩ D₁ = c₁ '' arm 0)
    (hc₀ : FinitePiecewiseAffineOn c₀ source) (hi₀ : InjOn c₀ source)
    (hc₁ : FinitePiecewiseAffineOn c₁ source) (hi₁ : InjOn c₁ source)
    (hc₀S : MapsTo c₀ source S₀) (hc₁S : MapsTo c₁ source S₁)
    (hc₀Q : ∀ p ∈ source, c₀ p ∈ Q₀ ↔ p.1 = 0 ∨ p.1 = 1)
    (hc₁Q : ∀ p ∈ source, c₁ p ∈ Q₁ ↔ p.1 = 0 ∨ p.1 = 1)
    (hhalf₀ : c₀ '' halfSource false ⊆ E₀) (hhalf₁ : c₁ '' halfSource true ⊆ D₁)
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁) (hE₁ : IsCompact E₁)
    (hS₀T : S₀ ⊆ T₀) (hD₀S : D₀ ⊆ S₀) (hD₁S : D₁ ⊆ S₁)
    (hD₀H : Disjoint D₀ H₀) (hc₀H : Disjoint (c₀ '' source) H₀)
    (hD₁H : Disjoint D₁ H₁)
    (hf₀ : PolyhedralPLInCharts e f₀ S₀) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hfi₀ : InjOn f₀ S₀) (hfi₁ : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ S₀ R) (hf₁R : MapsTo f₁ S₁ R)
    (hf₀O : MapsTo f₀ D₀ O) (hf₁O : MapsTo f₁ D₁ O)
    (hp₀ : ∀ x ∈ S₀, f₀ x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀)
    (hp₁ : ∀ x ∈ S₁, f₁ x ∈ frontier R ↔ x ∈ Q₁ ∪ H₁)
    (honly : ∀ x ∈ D₁, f₁ x ∈ f₀ '' S₀ → x ∈ c₁ '' arm 0)
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (hτR : MapsTo τ tube R) (hτO : MapsTo τ tube O)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (htrace₀ : ∀ z ∈ tube, τ z ∈ f₀ '' S₀ ↔ z.1.2 = -z.1.1)
    (htrace₁ : ∀ z ∈ tube, τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hsheet₀ : ∀ p ∈ source, f₀ (c₀ p) = τ ((p.2, -p.2), p.1))
    (hsheet₁ : ∀ p ∈ source, f₁ (c₁ p) = τ ((p.2, p.2), p.1)) :
    ∃ (N C U V : Set P2) (g : P2 → X),
      IsFinitePLBallPair P2 N (U ∪ c₀ '' arm (-1)) ∧
      IsFinitePLBallPair P2 C ((c₀ '' arm (-1)) ∪ V) ∧
      N ⊆ S₀ ∧ S₀ ⊆ N ∪ C ∧ N ∩ C = c₀ '' arm (-1) ∧
      Disjoint N H₀ ∧ c₀ '' arm 0 ⊆ N \ C ∧
      PolyhedralPLInCharts e g N ∧ InjOn g N ∧ MapsTo g N R ∧ MapsTo g N O ∧
      EqOn g f₀ (c₀ '' arm (-1)) ∧ Disjoint (g '' N) (f₁ '' S₁) ∧
      (∀ x ∈ N, g x ∈ f₀ '' S₀ ↔ x ∈ c₀ '' arm (-1)) ∧
      ∀ x ∈ N, g x ∈ frontier R ↔ x ∈ Q₀ := by
  obtain ⟨N, C, U, V, hN, hC, hU, hUZ, hNC, hNZ, hNQ, hNeq, _,
    hNS, hNH, hcenter, _⟩ := exists_enlarged_returning_disk hT₀ hc₀ hi₀ hc₀S hS₀T
      hD₀S hc₀Q hE₀ hcover₀ hcommon₀ hhalf₀ hD₀H hc₀H
  obtain ⟨B, V₁, _, hB, hV₁, hVZ, hBQ, hBD, htrimCover, htrim, hBcenter⟩ :=
    exists_trimmed_returning_disk hD₁ hDU₁ hc₁ hi₁ hc₁Q hhalf₁
  have hUW : U₀ ∩ (c₀ '' arm 0) = {c₀ (0, 0), c₀ (1, 0)} := by
    rw [← hDU₀, inter_assoc,
      inter_eq_right.mpr (inter_subset_right.trans (subset_union_right.trans hD₀.1))]
    exact proper_strip_arm_rim_contact (by norm_num) hc₀Q
  have hNproper (x : P2) (hx : x ∈ N) : f₀ x ∈ frontier R ↔ x ∈ U := by
    rw [hp₀ x (hNS hx)]
    constructor
    · rintro (hQ | hH)
      · exact hNQ.subset ⟨hx, hQ⟩
      · exact (disjoint_left.mp hNH hx hH).elim
    · exact fun h ↦ Or.inl (hNQ.superset h).2
  have hBproper (x : P2) (hx : x ∈ B) : f₁ x ∈ frontier R ↔ x ∈ V₁ := by
    rw [hp₁ x (hD₁S (hBD hx))]
    constructor
    · rintro (hQ | hH)
      · exact hBQ.subset ⟨hx, hQ⟩
      · exact (disjoint_left.mp hD₁H (hBD hx) hH).elim
    · exact fun h ↦ Or.inl (hBQ.superset h).2
  have hNO : MapsTo f₀ N O := by
    intro x hx
    rcases hNeq.subset hx with hx | ⟨p, hp, rfl⟩
    · exact hf₀O hx
    · rw [hsheet₀ p (halfSource_subset_source false hp)]
      exact hτO (originalStripSheet_mem_tube true (halfSource_subset_source false hp))
  have hBT : Disjoint (f₁ '' B) (f₀ '' S₀) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ht
    exact disjoint_left.mp hBcenter hx (honly x (hBD hx) ht)
  have hfar (t : Icc (0 : ℝ) 1) :
      f₀ (c₀ ((t : ℝ), -1)) = τ ((-1, 1), (t : ℝ)) := by
    simpa using hsheet₀ ((t : ℝ), -1) ⟨t.property, by norm_num⟩
  obtain ⟨g, hg, hgi, hgR, hgO, hgfix, hgavoid, hgtrace, hgproper⟩ :=
    exists_original_local_returning_arc_removal hR he hO hc₀ hi₀ hc₁ hi₁
      hD₀ hB hU₀ hV₁ hUW hVZ (returning_disk_negative_half_contact hcommon₀ hhalf₀)
      hDU₀ hNQ hc₀Q hNeq hN hU hUZ hS₀ hS₁ hE₁ hNS (hBD.trans hD₁S) hc₁S
      hcover₁ hcommon₁ htrim htrimCover hf₀ hf₁ hfi₀ hfi₁ hf₀R hf₁R hNO
      (fun _ hx ↦ hf₁O (hBD hx)) hNproper hBproper hτ hτi hτR hτO hτfront
      htrace₁ htrace₀ hBT hfar hsheet₁
  refine ⟨N, C, U, V, g, hN, hC, hNS, hS₀T.trans hNC.symm.subset, hNZ,
    hNH, hcenter, hg, hgi, hgR, hgO, hgfix, hgavoid, hgtrace, ?_⟩
  intro x hx
  exact (hgproper x hx).trans
    ⟨fun h ↦ (hNQ.superset h).2, fun h ↦ hNQ.subset ⟨hx, h⟩⟩

end PoincareConjecture.M76.Dehn.Annuli
