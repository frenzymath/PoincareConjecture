import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.NestedStageCorrection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.NestedCorrectedRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedDecrease
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OrdinaryPreservation

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip Topology
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)

theorem exists_essential_paired_stage_surgery
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q, (f x : V3) = h (coordinates x))
    (period : Circle ≃ₜ Q) {R : Set s.Carrier}
    (f₀ : P2 → s.Carrier) (hf₀ : PolyhedralPLInCharts s.charts f₀ Ann)
    (hfR : MapsTo f₀ Ann R)
    (hfproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (hwhole : ∀ b z, f₀ (annulusRimPoint b z) = s.annulusRim hS b (period z))
    (M : Annuli.SourceCircleDecomposition f₀ Ann)
    (hinterior : MapsTo f₀ (doubleLocusOn f₀ Ann) (interior R))
    (hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → f₀ x = f₀ y →
      Nonempty (Annuli.RawSourceCrossing s.charts f₀ Ann R x y))
    {l d : ℝ} (hd : 0 < d) (hwidth : 4 * d < l)
    (A : Fin 2 → Set P2) (B : ∀ k, OrientedPolygonCollar l d (A k)) (j : Fin 2)
    (hA : ∀ k, A k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (henclosing : annulusSquare 8 1 ⊆ (B j.rev).outer.inside)
    (hnested : closure (B j.rev).outer.inside ⊆ (B j).inner.inside)
    (i : Fin 2 → M.Index)
    (hmiddle : ∀ k, (fun p : squareAnnulus l d ↦ ((B k).chart p : P2)) ''
      {p | depth l p = 0} = M.pieces (i k))
    (htrace : ∀ k x, x ∈ A k → x ∈ doubleLocusOn f₀ Ann → x ∈ M.pieces (i k))
    (τ : (P2 × ℝ) → s.Carrier) (hτ : PolyhedralPLInCharts s.charts τ (identityTube l d))
    (hτR : MapsTo τ (identityTube l d) (interior R))
    (hfib : ∀ z ∈ identityTube l d, ∀ w ∈ identityTube l d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * l)) = (w.2 : AddCircle (4 * l)))
    (hvalue : ∀ (k : Fin 2) (t : ℝ) (_ht : t ∈ Icc 0 (4 * l)) (u : Icc (-d) d),
      f₀ ((B k).chart ⟨annulusMap l (by linarith) ((t : AddCircle (4 * l)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, t))
    (hpre : ∀ x ∈ Ann, f₀ x ∈ τ '' identityTube l d ↔ x ∈ A j ∪ A j.rev) :
    ∃ G : P2 → s.Carrier,
      PolyhedralPLInCharts s.charts G Ann ∧ MapsTo G Ann R ∧
      (∀ x ∈ Ann, G x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      (∀ b z, G (annulusRimPoint b z) = s.annulusRim hS b (period z)) ∧
      IsLocallyInjective (fun x : Ann ↦ G x) ∧
      IsCompact (doubleLocusOn G Ann) ∧
      MapsTo G (doubleLocusOn G Ann) (interior R) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → G x = G y →
        Nonempty (Annuli.RawSourceCrossing s.charts G Ann R x y)) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
        x ≠ y → x ≠ z → G x = G y → G x = G z → y = z) ∧
      Nonempty (Annuli.SourceCircleDecomposition G Ann) ∧
      Nat.card (ConnectedComponents (doubleLocusOn G Ann)) <
        Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann)) := by
  obtain ⟨D⟩ := Annuli.nonempty_nested_resolving_cylinder s.charts B j s.compatible
    hd hwidth (b := d / 2) (by linarith) (by linarith) (L := 8) (d := 1)
    (by norm_num) (by norm_num) hA henclosing hnested f₀ hf₀ τ hτ hfib hvalue hpre
  obtain ⟨H, G, hH, hG, hGv, hGwhole, _, hGimage, hcount, hproper⟩ :=
    exists_nested_stage_whole_rim_correction L retained s hS hvalues period D hA
      henclosing hwhole
  have hdepth : ∀ k (p : squareAnnulus l d),
      ((B k).chart p : P2) ∈ doubleLocusOn f₀ Ann → depth l p = 0 := by
    intro k p hp
    obtain ⟨q, hq, heq⟩ := (hmiddle k).symm.subset
      (htrace k ((B k).chart p) ((B k).chart p).property hp)
    exact ((B k).chart.injective (Subtype.ext heq)) ▸ hq
  obtain ⟨c₀, c, U, W, H₁, _, _, _, hci, hcc, _, hcmaps, hckeep, hcrel, hcdouble,
    hUK, hWS, hU, hW, _, hHkeep, _, hnew⟩ :=
      D.exists_corrected_retained_source H hH hGv hd hnested hdepth
  let Kret := (annulusSquare 8 (-1) \ (B j).outer.inside) ∪
    (closure (B j.rev).inner.inside \ interior (annulusSquare 8 1))
  have hKret : IsClosed Kret :=
    (D.copyO_PL.choose_spec.1.isCompact.union D.copyI_PL.choose_spec.1.isCompact).isClosed
  have hKAnn : Kret ⊆ Ann := union_subset D.outer_source D.inner_source
  obtain ⟨K, hK, hKS, _⟩ := hH.choose_spec.1
  have hAnn : IsCompact Ann := hKS ▸ K.isCompact_space_of_finite hK
  let p : doubleLocusOn f₀ Ann → doubleLocusOn f₀ Ann := fun x ↦
    ⟨M.partner ⟨x, M.space.symm.subset x.property⟩,
      M.space.subset (M.partner ⟨x, M.space.symm.subset x.property⟩).property⟩
  have hp : Continuous p := (continuous_subtype_val.comp
    (M.partner.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  have hpvalue (x) : f₀ (p x) = f₀ x := M.value ⟨x, M.space.symm.subset x.property⟩
  have hpfree (x) : (p x : P2) ≠ x := M.free ⟨x, M.space.symm.subset x.property⟩
  have hpunique (x : doubleLocusOn f₀ Ann) (y : P2) (hy : y ∈ Ann)
      (heq : f₀ x = f₀ y) (hne : (x : P2) ≠ y) : y = (p x : P2) :=
    M.unique ⟨x, M.space.symm.subset x.property⟩ y hy hne heq
  have hcompact : IsCompact (doubleLocusOn f₀ Ann) :=
    M.space ▸ M.graph.isCompact_space_of_finite M.finite
  obtain ⟨hGc, hGclosed, hGinterior, hGunique, hGcross, hGlocal⟩ :=
    Annuli.ordinary_crossings_preserved_by_retained_copy hKAnn hKret hAnn hAnn hcompact
      p hp hpvalue hpfree hpunique hinterior hcross c hci hcc hckeep hcrel hcdouble
      (hUK.trans hKAnn) hWS hU hW hf₀.continuousOn hG.continuousOn H₁ hHkeep hnew
  have hGmaps : MapsTo G Ann R := by
    intro x hx
    have him := D.image.subset (hGimage.subset ⟨x, hx, rfl⟩)
    rcases him with (⟨y, hy, heq⟩ | ⟨y, hy, heq⟩) | ⟨y, hy, heq⟩
    · exact heq ▸ hfR (D.outer_source hy)
    · obtain ⟨z, hz, hzv⟩ := D.annulus_tube ⟨y, hy, rfl⟩
      rw [← heq, ← hzv]
      exact interior_subset (hτR hz)
    · exact heq ▸ hfR (D.inner_source hy)
  have hτfront : Disjoint (τ '' identityTube l d) (frontier R) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact disjoint_left.mp disjoint_interior_frontier (hτR hz) hx
  have hnext : Nonempty (Annuli.SourceCircleDecomposition G Ann) := by
    rw [← hKS]
    exact Annuli.nonempty_sourceCircleDecomposition s.compatible K hK
      (by simpa only [hKS] using hG) (by simpa only [hKS] using hGmaps)
      (by simpa only [hKS] using hGclosed) (by simpa only [hKS] using hGinterior)
      (by simpa only [hKS] using hGcross) (by simpa only [hKS] using hGunique)
  exact ⟨G, hG, hGmaps, fun x hx ↦ hproper (frontier R) hfproper hτfront ⟨x, hx⟩,
    hGwhole, hGlocal, hGc, hGinterior, hGcross, hGunique, hnext,
    hcount.trans_lt (D.double_component_count_lt M i hd hnested hmiddle htrace)⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
