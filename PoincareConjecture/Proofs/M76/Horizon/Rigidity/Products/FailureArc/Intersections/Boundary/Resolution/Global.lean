import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Prepared
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Preservation



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_global_original_returning_arc_removal
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R O F : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hO : IsOpen O)
    (hOmark : O ∩ frontier R ⊆ F)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {T₀ Q₀ D₀ E₀ U₀ H₀ D₁ E₁ U₁ S₁ Q₁ H₁ : Set P2}
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
    (hc₀S : MapsTo c₀ source J.space) (hc₁S : MapsTo c₁ source S₁)
    (hc₀Q : ∀ p ∈ source, c₀ p ∈ Q₀ ↔ p.1 = 0 ∨ p.1 = 1)
    (hc₁Q : ∀ p ∈ source, c₁ p ∈ Q₁ ↔ p.1 = 0 ∨ p.1 = 1)
    (hhalf₀ : c₀ '' halfSource false ⊆ E₀) (hhalf₁ : c₁ '' halfSource true ⊆ D₁)
    (hS₁ : IsCompact S₁) (hE₁ : IsCompact E₁)
    (hS₀T : J.space ⊆ T₀) (hD₀S : D₀ ⊆ J.space) (hD₁S : D₁ ⊆ S₁)
    (hD₀H : Disjoint D₀ H₀) (hc₀H : Disjoint (c₀ '' source) H₀)
    (hD₁H : Disjoint D₁ H₁)
    (hf₀ : PolyhedralPLInCharts e f₀ J.space) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hfi₀ : InjOn f₀ J.space) (hfi₁ : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ J.space R) (hf₁R : MapsTo f₁ S₁ R)
    (hf₀O : MapsTo f₀ D₀ O) (hf₁O : MapsTo f₁ D₁ O)
    (hp₀ : ∀ x ∈ J.space, f₀ x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀)
    (hp₁ : ∀ x ∈ S₁, f₁ x ∈ frontier R ↔ x ∈ Q₁ ∪ H₁)
    (hfmark : MapsTo f₀ (J.space ∩ Q₀) F)
    (honly : ∀ x ∈ D₁, f₁ x ∈ f₀ '' J.space → x ∈ c₁ '' arm 0)
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (hτR : MapsTo τ tube R) (hτO : MapsTo τ tube O)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (htrace₀ : ∀ z ∈ tube, τ z ∈ f₀ '' J.space ↔ z.1.2 = -z.1.1)
    (htrace₁ : ∀ z ∈ tube, τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hsheet₀ : ∀ p ∈ source, f₀ (c₀ p) = τ ((p.2, -p.2), p.1))
    (hsheet₁ : ∀ p ∈ source, f₁ (c₁ p) = τ ((p.2, p.2), p.1))
    (pieces : κ → Set P2) (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)))
    (hpieces : ⋃ i, pieces i = J.space ∩ f₀ ⁻¹' (f₁ '' S₁))
    (hconn : ∀ i, IsConnected (pieces i)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space ↦ k x) ∧ MapsTo k J.space R ∧
      EqOn k f₀ (J.space ∩ H₀) ∧ MapsTo k (J.space ∩ Q₀) F ∧
      (∀ x ∈ J.space, k x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀) ∧
      J.space ∩ k ⁻¹' (f₁ '' S₁) ⊆ J.space ∩ f₀ ⁻¹' (f₁ '' S₁) ∧
      EqOn k f₀ (J.space ∩ k ⁻¹' (f₁ '' S₁)) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (f₁ '' S₁) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f₀ ⁻¹' (f₁ '' S₁) : Set P2)) ∧
      ∃ W : Set X, IsOpen W ∧ (f₁ '' S₁) ∩ (k '' J.space) ⊆ W ∧
        ∀ z ∈ W, z ∈ k '' J.space ↔ z ∈ f₀ '' J.space := by
  obtain ⟨N, C, U, V, g, hN, hC, hNS, hcover, hcommon, hNH, hremoved,
    hg, hgi, hgR, hgO, hgfix, hgavoid, hgtrace, hgproper⟩ :=
    exists_prepared_original_returning_arc_removal hR he hO hT₀ hD₀ hE₀ hU₀ hDU₀
      hcover₀ hcommon₀ hD₁ hDU₁ hcover₁ hcommon₁ hc₀ hi₀ hc₁ hi₁ hc₀S hc₁S
      hc₀Q hc₁Q hhalf₀ hhalf₁ (J.isCompact_space_of_finite hJ) hS₁ hE₁ hS₀T hD₀S hD₁S
      hD₀H hc₀H hD₁H hf₀ hf₁ hfi₀ hfi₁ hf₀R hf₁R hf₀O hf₁O hp₀ hp₁ honly
      hτ hτi hτR hτO hτfront htrace₀ htrace₁ hsheet₀ hsheet₁
  have h00 : ((0, 0) : P2) ∈ source := by norm_num [source]
  have hcenter : c₀ (0, 0) ∈ c₀ '' arm 0 := ⟨(0, 0), by norm_num [arm], rfl⟩
  have hvalue : f₁ (c₁ (0, 0)) = f₀ (c₀ (0, 0)) := by
    rw [hsheet₀ _ h00, hsheet₁ _ h00]
    simp
  have hdeleted : ((J.space ∩ f₀ ⁻¹' (f₁ '' S₁)) \ C).Nonempty :=
    ⟨c₀ (0, 0), ⟨hc₀S h00, ⟨c₁ (0, 0), hc₁S h00, hvalue⟩⟩, (hremoved hcenter).2⟩
  obtain ⟨k, hk, _, hke, hkN, hkC, hkimage, hkinter, hkcount⟩ :=
    exists_original_boundary_replacement_with_count_decrease he.compatible J hJ hN hC hNS
      hcover hcommon hf₀ hfi₀ hg hgi hgfix hgtrace hgavoid pieces hclosed hdis hpieces hconn hdeleted
  obtain ⟨hkR, hkH, hkproper, hkF⟩ := pasted_boundary_disk_preserves_marks hcover hNH hkN hkC
    hf₀R hgR hgO hp₀ hgproper hfmark hOmark
  refine ⟨k, hk, hke, hkR, hkH, hkF, hkproper, ?_, ?_, hkcount, ?_⟩
  · exact hkinter.subset.trans inter_subset_left
  · intro x hx
    have hxc := hkinter.subset hx
    exact hkC ⟨hxc.1.1, hxc.2⟩
  · exact exists_open_agreement_of_boundary_disk_paste hN hNS hcover hcommon hf₀ hfi₀
      hg hgfix hgavoid hkimage

end PoincareConjecture.M76.Dehn.Annuli
