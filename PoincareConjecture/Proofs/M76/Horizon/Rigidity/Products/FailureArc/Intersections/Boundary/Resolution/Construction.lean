import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Global
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Construction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.MarkedFrontierNeighborhood

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_returning_arc_removal_of_cut_disks
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R F : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (hF : F ⊆ frontier R) (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (J K : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) (hK : K.faces.Finite)
    {T₀ Q₀ H₀ Q₁ H₁ C D D₀ E₀ U₀ V₀ D₁ E₁ U₁ V₁ : Set P2}
    (hT₀ : IsFinitePLBallPair P2 T₀ Q₀)
    (hQ₀ : IsClosed Q₀) (hH₀ : IsClosed H₀) (hQH₀ : Disjoint Q₀ H₀)
    (hQ₁ : IsClosed Q₁) (hH₁ : IsClosed H₁) (hQH₁ : Disjoint Q₁ H₁)
    (hrim₀ : Q₀ ∪ H₀ ⊆ J.space) (hrim₁ : Q₁ ∪ H₁ ⊆ K.space)
    (hD₀ : IsFinitePLBallPair P2 D₀ (U₀ ∪ C))
    (hE₀ : IsFinitePLBallPair P2 E₀ (C ∪ V₀))
    (hU₀ : IsFinitePLBallPair ℝ U₀ (U₀ ∩ C))
    (hDU₀ : D₀ ∩ Q₀ = U₀) (hEV₀ : E₀ ∩ Q₀ = V₀)
    (hcover₀ : D₀ ∪ E₀ = T₀) (hcommon₀ : D₀ ∩ E₀ = C)
    (hD₁ : IsFinitePLBallPair P2 D₁ (U₁ ∪ D))
    (hE₁ : IsFinitePLBallPair P2 E₁ (D ∪ V₁))
    (hDU₁ : D₁ ∩ Q₁ = U₁) (hcover₁ : K.space ⊆ D₁ ∪ E₁)
    (hcommon₁ : D₁ ∩ E₁ = D)
    (hS₀T : J.space ⊆ T₀) (hD₀S : D₀ ⊆ J.space) (hD₁S : D₁ ⊆ K.space)
    (hD₀H : Disjoint D₀ H₀) (hD₁H : Disjoint D₁ H₁)
    (hCball : IsFinitePLBallPair ℝ C (C ∩ (Q₀ ∪ H₀)))
    {f₀ f₁ : P2 → X}
    (hf₀ : PolyhedralPLInCharts e f₀ J.space) (hf₁ : PolyhedralPLInCharts e f₁ K.space)
    (hfi₀ : InjOn f₀ J.space) (hfi₁ : InjOn f₁ K.space)
    (hf₀R : MapsTo f₀ J.space R) (hf₁R : MapsTo f₁ K.space R)
    (hp₀ : ∀ x ∈ J.space, f₀ x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀)
    (hp₁ : ∀ x ∈ K.space, f₁ x ∈ frontier R ↔ x ∈ Q₁ ∪ H₁)
    (hfmark₀ : MapsTo f₀ (J.space ∩ Q₀) F) (hfmark₁ : MapsTo f₁ (K.space ∩ Q₁) F)
    (himage : f₀ '' C = f₁ '' D)
    (honly : ∀ x ∈ D₁, f₁ x ∈ f₀ '' J.space → x ∈ D)
    (hrest : IsClosed ((J.space ∩ f₀ ⁻¹' (f₁ '' K.space)) \ C))
    (hboundary : ∀ x ∈ J.space, f₀ x ∈ f₁ '' K.space → f₀ x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f₀ '' J.space) (f₁ '' K.space) (f₀ x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ J.space, f₀ x ∈ f₁ '' K.space → f₀ x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f₀ '' J.space) (f₁ '' K.space) (f₀ x) false))
    (pieces : κ → Set P2) (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)))
    (hpieces : ⋃ i, pieces i = J.space ∩ f₀ ⁻¹' (f₁ '' K.space))
    (hconn : ∀ i, IsConnected (pieces i)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space ↦ k x) ∧ MapsTo k J.space R ∧
      EqOn k f₀ (J.space ∩ H₀) ∧ MapsTo k (J.space ∩ Q₀) F ∧
      (∀ x ∈ J.space, k x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀) ∧
      J.space ∩ k ⁻¹' (f₁ '' K.space) ⊆ J.space ∩ f₀ ⁻¹' (f₁ '' K.space) ∧
      EqOn k f₀ (J.space ∩ k ⁻¹' (f₁ '' K.space)) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (f₁ '' K.space) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f₀ ⁻¹' (f₁ '' K.space) : Set P2)) ∧
      (∀ x ∈ J.space, k x ∈ f₁ '' K.space → k x ∈ frontier R →
        ∃ B : OriginalSurfacePairChart e (k '' J.space) (f₁ '' K.space) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      (∀ x ∈ J.space, k x ∈ f₁ '' K.space → k x ∈ interior R →
        Nonempty (OriginalSurfacePairChart e (k '' J.space) (f₁ '' K.space) (k x) false)) ∧
      ∃ W : Set X, IsOpen W ∧ (f₁ '' K.space) ∩ (k '' J.space) ⊆ W ∧
        ∀ z ∈ W, z ∈ k '' J.space ↔ z ∈ f₀ '' J.space := by
  have hCD₀ : C ⊆ D₀ := subset_union_right.trans hD₀.1
  have hDD₁ : D ⊆ D₁ := subset_union_right.trans hD₁.1
  have hCS : C ⊆ J.space := hCD₀.trans hD₀S
  have hDS : D ⊆ K.space := hDD₁.trans hD₁S
  obtain ⟨O, hO, hRO, hOF⟩ := exists_open_frontier_mark_neighborhood hF hFopen
  have hDO₀ : MapsTo f₀ D₀ O := by
    intro x hx
    apply hRO
    by_cases hb : f₀ x ∈ frontier R
    · apply Or.inr
      rcases (hp₀ x (hD₀S hx)).mp hb with hq | hh
      · exact hfmark₀ ⟨hD₀S hx, hq⟩
      · exact (disjoint_left.mp hD₀H hx hh).elim
    · exact Or.inl (by_contra fun hn ↦ hb ⟨subset_closure (hf₀R (hD₀S hx)), hn⟩)
  have hDO₁ : MapsTo f₁ D₁ O := by
    intro x hx
    apply hRO
    by_cases hb : f₁ x ∈ frontier R
    · apply Or.inr
      rcases (hp₁ x (hD₁S hx)).mp hb with hq | hh
      · exact hfmark₁ ⟨hD₁S hx, hq⟩
      · exact (disjoint_left.mp hD₁H hx hh).elim
    · exact Or.inl (by_contra fun hn ↦ hb ⟨subset_closure (hf₁R (hD₁S hx)), hn⟩)
  obtain ⟨I⟩ := nonempty_originalIntervalTube he J K hJ hK f₀ f₁ hf₀ hf₁ hfi₀ hfi₁
    hf₀R hf₁R (Q₀ ∪ H₀) (Q₁ ∪ H₁) hrim₀ hrim₁ hp₀ hp₁ hboundary hinterior
    C D hCS hDS hCball himage hrest hO ((image_mono hCD₀).trans hDO₀.image_subset)
  obtain ⟨_, hIH₀, _, hIH₁⟩ := I.returning_source_rims hQ₀ hH₀ hQH₀ hQ₁ hH₁ hQH₁
    hp₀ hp₁ (hD₀H.mono_left hCD₀) (hD₁H.mono_left hDD₁)
  obtain ⟨c₀, c₁, τ, hc₀, hc₁, hci₀, hci₁, hc₀S, hc₁S, hc₀image, hc₁image,
    hcenter₀, hcenter₁, _, hhalf₀, hhalf₁, _, hτ, hτe, hτR, hτO, _,
    hsheet₀, hsheet₁, htrace₀, htrace₁, hτfront⟩ :=
    exists_cut_oriented_original_interval_tube I hD₀ hE₀ hD₁ hE₁
      (hS₀T.trans hcover₀.symm.subset) hcover₁ hcommon₀ hcommon₁
  have hc₀H : Disjoint (c₀ '' source) H₀ := hc₀image.symm ▸ hIH₀
  have hc₁H : Disjoint (c₁ '' source) H₁ := hc₁image.symm ▸ hIH₁
  have hc₀Q (p : P2) (hp : p ∈ source) : c₀ p ∈ Q₀ ↔ p.1 = 0 ∨ p.1 = 1 := by
    have hnot : c₀ p ∉ H₀ := fun hh ↦ disjoint_left.mp hc₀H ⟨p, hp, rfl⟩ hh
    have hp' := hp₀ (c₀ p) (hc₀S hp)
    rw [hsheet₀ p hp, hτfront ((p.2, -p.2), p.1)
      (originalStripSheet_mem_tube true hp)] at hp'
    simpa only [mem_union, hnot, or_false] using hp'.symm
  have hc₁Q (p : P2) (hp : p ∈ source) : c₁ p ∈ Q₁ ↔ p.1 = 0 ∨ p.1 = 1 := by
    have hnot : c₁ p ∉ H₁ := fun hh ↦ disjoint_left.mp hc₁H ⟨p, hp, rfl⟩ hh
    have hp' := hp₁ (c₁ p) (hc₁S hp)
    rw [hsheet₁ p hp, hτfront ((p.2, p.2), p.1)
      (originalStripSheet_mem_tube false hp)] at hp'
    simpa only [mem_union, hnot, or_false] using hp'.symm
  have hUends : U₀ ∩ C = {c₀ (0, 0), c₀ (1, 0)} := by
    rw [← hDU₀, inter_assoc, inter_eq_right.mpr (inter_subset_right.trans hCD₀), ← hcenter₀]
    exact proper_strip_arm_rim_contact (by norm_num) hc₀Q
  have hE₀' : IsFinitePLBallPair P2 E₀ ((E₀ ∩ Q₀) ∪ c₀ '' arm 0) := by
    rw [hEV₀, hcenter₀]
    simpa only [union_comm] using hE₀
  have hEi₁ : E₁ ∩ D₁ = c₁ '' arm 0 := by rw [inter_comm, hcommon₁, hcenter₁]
  have hfi (c : P2 → P2) (h : IsEmbedding (fun p : source ↦ c p)) : InjOn c source :=
    fun x hx y hy hxy ↦ congrArg Subtype.val (h.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hτi : InjOn τ tube := fun x hx y hy hxy ↦
    congrArg Subtype.val (hτe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨k, hk, hki, hkR, hkH, hkF, hkproper, hksub, hkkeep, hkcount, W, hW, hin, hagree⟩ :=
    exists_global_original_returning_arc_removal hR he hO hOF.subset J hJ hT₀
    (hcenter₀.symm ▸ hD₀) hE₀' (hUends ▸ hU₀) hDU₀ hcover₀
    (hcommon₀.trans hcenter₀.symm) (hcenter₁.symm ▸ hD₁) hDU₁
    (hcover₁.trans (union_comm D₁ E₁).subset) hEi₁ hc₀ (hfi c₀ hci₀) hc₁ (hfi c₁ hci₁)
    hc₀S hc₁S hc₀Q hc₁Q hhalf₀ hhalf₁ (K.isCompact_space_of_finite hK) hE₁.isCompact
    hS₀T hD₀S hD₁S hD₀H hc₀H hD₁H hf₀ hf₁ hfi₀ hfi₁ hf₀R hf₁R hDO₀ hDO₁
    hp₀ hp₁ hfmark₀ (fun x hx ht ↦ hcenter₁.superset (honly x hx ht))
    hτ hτi hτR hτO hτfront htrace₀ htrace₁ hsheet₀ hsheet₁ pieces hclosed hdis hpieces hconn
  obtain ⟨hb, hi⟩ := original_pair_charts_after_local_replacement hW hin hagree hkkeep hboundary hinterior
  exact ⟨k, hk, hki, hkR, hkH, hkF, hkproper, hksub, hkkeep, hkcount, hb, hi,
    W, hW, hin, hagree⟩

end PoincareConjecture.M76.Dehn.Annuli
