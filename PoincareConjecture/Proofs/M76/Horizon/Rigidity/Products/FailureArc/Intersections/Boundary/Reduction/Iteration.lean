import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Canonical
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.Iteration







set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "First" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem exists_original_annulus_with_all_components_meeting_first_rim
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (F : Bool → Set X)
    (hR : IsCompact R) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F true))
    (hFdis : Disjoint (F false) (F true)) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann) (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hflast : MapsTo f (Ann ∩ Last) (F true)) (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧ IsEmbedding (fun x : Ann ↦ k x) ∧
      MapsTo k Ann R ∧ EqOn k f (Ann ∩ First) ∧ MapsTo k (Ann ∩ Last) (F true) ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ F false ↔ depth 8 x = -1) ∧
      ((k '' Ann) ∩ (g '' Ann)) ∩ F false = {p} ∧
      Ann ∩ k ⁻¹' (g '' Ann) ⊆ Ann ∩ f ⁻¹' (g '' Ann) ∧
      EqOn k f (Ann ∩ k ⁻¹' (g '' Ann)) ∧
      Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) ≤
        Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) ∧
      (∀ x : (Ann ∩ g ⁻¹' (k '' Ann) : Set P2),
        ∃ y : (Ann ∩ g ⁻¹' (k '' Ann) : Set P2),
          ConnectedComponents.mk x = ConnectedComponents.mk y ∧ depth 8 (y : P2) = -1) ∧
      (∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
        ∃ B : OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      ∀ x ∈ Ann \ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) false) := by
  classical
  generalize hn : Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    obtain ⟨m, hm, hmi, hmR, hmfront, hmp, hmsub, hmkeep, hmcount, hmmeet, hmb, hmint⟩ :=
      CircleResolution.exists_original_annulus_with_all_components_meeting_boundary hR he (hF false)
        hf hg hfi hgi hfR hgR hfp hgp hfmark hgmark p hpoint hboundary hinterior
    have hminj : InjOn m Ann := by
      intro x hx y hy hxy
      exact congrArg Subtype.val (hmi.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
    have hmmark : ∀ x ∈ Ann, m x ∈ F false ↔ depth 8 x = -1 := by
      intro x hx
      exact (CircleResolution.proper_rim_fixed_mark_iff (hF false) hfp hmp hmfront x hx).trans
        (hfmark x hx)
    have hmpoint : ((m '' Ann) ∩ (g '' Ann)) ∩ F false = {p} :=
      (CircleResolution.proper_rim_fixed_marked_intersection (hF false) hfp hmp hmfront).trans hpoint
    have hmfirst : EqOn m f (Ann ∩ First) := by
      intro x hx
      exact hmfront ((mem_frontier_planar_annulus_iff x).mpr (Or.inl hx.2))
    have hmlast : MapsTo m (Ann ∩ Last) (F true) := by
      intro x hx
      rw [hmfront ((mem_frontier_planar_annulus_iff x).mpr (Or.inr hx.2))]
      exact hflast hx
    rcases canonical_returning_reduction_or_components_meet_first_rim F hR he hF hFopen hFdis
      hm hg hminj hgi hmR hgR hmp hgp hmmark hgmark hmlast hglast p hmpoint hmmeet hmb hmint with
      hterminal | hstep
    · exact ⟨m, hm, hmi, hmR, hmfirst, hmlast, hmp, hmmark, hmpoint, hmsub, hmkeep,
        hmcount.trans hn.le, hterminal, hmb, hmint⟩
    · obtain ⟨k, hk, hki, hkR, hkfirst, hklast, hkp, hkmark, hkpoint, hksub, hkkeep,
        hkcount, hkb, hkint⟩ := hstep
      have hkinj : InjOn k Ann := by
        intro x hx y hy hxy
        exact congrArg Subtype.val (hki.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
      have hlt : Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) < n :=
        hkcount.trans_le (hmcount.trans hn.le)
      obtain ⟨k', hk', hki', hkR', hkfirst', hklast', hkp', hkmark', hkpoint', hksub', hkkeep',
        hkcount', hkmeet', hkb', hkint'⟩ :=
        ih _ hlt hk hkinj hkR hkp hkmark hklast hkpoint hkb hkint rfl
      refine ⟨k', hk', hki', hkR', ?_, hklast', hkp', hkmark', hkpoint',
        hksub'.trans (hksub.trans hmsub), ?_, hkcount'.trans hlt.le, hkmeet', hkb', hkint'⟩
      · intro x hx
        exact (hkfirst' hx).trans ((hkfirst hx).trans (hmfirst hx))
      · intro x hx
        exact (hkkeep' hx).trans ((hkkeep (hksub' hx)).trans (hmkeep x (hksub (hksub' hx))))

end PoincareConjecture.M76.Dehn.Annuli
