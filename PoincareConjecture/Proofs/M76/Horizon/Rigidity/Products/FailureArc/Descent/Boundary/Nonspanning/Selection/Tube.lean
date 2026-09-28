import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.StateGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.MarkedEnds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.Construction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.OriginalStripDoubleLocus



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

namespace Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "T" => spanningOuterSquare
local notation "D" => spanningInnerSquare

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}

theorem exists_outer_nonspanning_tube
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (K : SourceDoubleComponents s.charts A.map (T \ interior D)
      (frontier T ∪ frontier D) (s.projection ⁻¹' R))
    (i : K.Index) (hmeet : (K.pieces i ∩ frontier T).Nonempty)
    (havoid : Disjoint (K.pieces i) (frontier D)) :
    ∃ (c : Bool → P2 → P2) (τ : (P2 × ℝ) → s.Carrier),
      (∀ j, FinitePiecewiseAffineOn (c j) source ∧ InjOn (c j) source ∧
        MapsTo (c j) source (T \ interior D)) ∧
      Disjoint (c false '' source) (c true '' source) ∧
      Disjoint (c false '' source ∪ c true '' source) D ∧
      (∀ j p, p ∈ source → (c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1)) ∧
      PolyhedralPLInCharts s.charts τ tube ∧ InjOn τ tube ∧ MapsTo τ tube (s.projection ⁻¹' R) ∧
      (∀ j p, p ∈ source → A.map (c j p) = τ (originalStripSheet j p)) ∧
      (T \ interior D) ∩ A.map ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source ∧
      (∀ j, c j '' arm 0 = K.pieces (if j then K.mate i else i)) ∧
      (∀ z ∈ tube, τ z ∈ frontier (s.projection ⁻¹' R) ↔ z.2 = 0 ∨ z.2 = 1) ∧
      (∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → s.projection (τ z) ∈ F false) := by
  have hsource : T \ interior D = Ann := spanning_squares_source
  have hDin : frontier D ⊆ Ann := by
    intro x hx
    rw [mem_squareAnnulus_iff_depth, mem_Icc, (spanning_inner_frontier x).mp hx]
    norm_num
  have hDcompact : IsCompact (frontier D) :=
    spanningInnerSquare_ball.isCompact.of_isClosed_subset isClosed_frontier
      spanningInnerSquare_ball.isCompact.isClosed.frontier_subset
  have hprotected : IsClosed (A.map '' frontier D) :=
    (hDcompact.image_of_continuousOn (A.piecewiseAffine.continuousOn.mono hDin)).isClosed
  have hfront : ∀ x ∈ T \ interior D,
      A.map x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ frontier T ∪ frontier D := by
    simpa only [hsource, spanning_squares_rim] using A.proper
  have hmark0 (x : P2) (hx : x ∈ T \ interior D) (hq : x ∈ frontier T) :
      s.projection (A.map x) ∈ F false :=
    A.mark_of_depth false ⟨x, hsource ▸ hx⟩ ((spanning_outer_frontier x).mp hq)
  have hphysicalavoid : Disjoint (A.map '' K.pieces i) (A.map '' frontier D) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hxi, rfl⟩ ⟨y, hyD, hxy⟩
    have hx : x ∈ T \ interior D := (K.space ▸ K.pieces_subset i hxi).1
    have hymark := A.mark_of_depth true ⟨y, hDin hyD⟩ ((spanning_inner_frontier y).mp hyD)
    have hxfront : A.map x ∈ frontier (s.projection ⁻¹' R) := by
      rw [s.frontier_region]
      exact hxy ▸ hF true hymark
    have hxouter : x ∈ frontier T := ((hfront x hx).mp hxfront).resolve_right
      (fun hh ↦ disjoint_left.mp havoid hxi hh)
    exact disjoint_left.mp hdis (hmark0 x hx hxouter) (hxy ▸ hymark)
  obtain ⟨W, hW, hAW, htrace⟩ := A.exists_original_mark_neighborhood hF hopen
  let V := (s.projection ⁻¹' W) ∩ (A.map '' frontier D)ᶜ
  have hV : IsOpen V := (hW.preimage s.projection.continuous).inter hprotected.isOpen_compl
  have hKV : A.map '' K.pieces i ⊆ V := by
    rintro _ ⟨x, hxi, rfl⟩
    have hx : x ∈ T \ interior D := (K.space ▸ K.pieces_subset i hxi).1
    exact ⟨hAW (hsource ▸ hx), fun hh ↦ disjoint_left.mp hphysicalavoid ⟨x, hxi, rfl⟩ hh⟩
  have hball := (K.interval_iff_meets_rim i).mpr
    (hmeet.mono (inter_subset_inter_right _ subset_union_left))
  obtain ⟨c, τ, hcs, hcd, hτ, hτemb, hτR, hτV, hval, hfull, hcenter, hτfront, hrim⟩ :=
    K.exists_interval_tube_source_strips (hsource.symm ▸ A.piecewiseAffine)
      (s.plDomain_region he) i hball (hsource.symm ▸ A.region) hfront hV hKV
  have hcavoid (j : Bool) (p : P2) (hp : p ∈ source) : c j p ∉ frontier D := by
    intro hD
    have hh := (hτV (originalStripSheet_mem_tube j hp)).2
    exact hh ⟨c j p, hD, hval j p hp⟩
  have hcD (j : Bool) (p : P2) (hp : p ∈ source) : c j p ∉ D := by
    intro hh
    apply hcavoid j p hp
    exact ⟨subset_closure hh, (hcs j).2.2 hp |>.2⟩
  have hcouter (j : Bool) (p : P2) (hp : p ∈ source) :
      c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1 := by
    have hh := hrim j p hp
    simpa only [mem_union, or_iff_left (hcavoid j p hp)] using hh
  have hprojfront : ∀ z ∈ tube, s.projection (τ z) ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 := by
    simpa only [s.frontier_region, mem_preimage] using hτfront
  have hends (t : unitInterval) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
      ∀ z ∈ tube, z.2 = t → s.projection (τ z) ∈ F false := by
    have hz : ((t : ℝ), 0) ∈ source := ⟨t.property, by norm_num⟩
    have hstart := hmark0 _ ((hcs false).2.2 hz) ((hcouter false _ hz).mpr ht)
    have hcenter' : s.projection (τ ((0, 0), t)) ∈ F false := by
      simpa [hval false _ hz, originalStripSheet] using hstart
    exact tube_end_mapsTo_original_mark F hopen hdis (s.projection ∘ τ)
      (s.projection.continuous.comp_continuousOn hτ.continuousOn)
      (fun z hz ↦ (hτV hz).1) htrace.subset hprojfront false t ht hcenter'
  refine ⟨c, τ, ?_, hcd, ?_, hcouter, hτ, ?_, hτR, hval, hfull, hcenter, hτfront, ?_⟩
  · intro j
    refine ⟨(hcs j).1, ?_, (hcs j).2.2⟩
    intro x hx y hy hh
    exact congrArg Subtype.val ((hcs j).2.1.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hh)
  · apply disjoint_left.mpr
    rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) hh
    · exact hcD false p hp hh
    · exact hcD true p hp hh
  · intro x hx y hy hh
    exact congrArg Subtype.val (hτemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hh)
  · intro z hz ht
    rcases ht with ht | ht
    · exact hends 0 (Or.inl rfl) z hz ht
    · exact hends 1 (Or.inr rfl) z hz ht

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
