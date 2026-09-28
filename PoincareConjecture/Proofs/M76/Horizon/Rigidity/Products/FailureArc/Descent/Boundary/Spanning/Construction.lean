import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.ExactFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.Ordinary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.ComponentCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.Candidate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.BothRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.LiteralPartner



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => (Set.ofPred (fun x : P2 ↦ depth 8 x = -1 ∨ depth 8 x = 1))

theorem exists_essential_ordinary_spanning_surgery
    {X Y ι : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : Bool → P2 → P2) (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source)
    (hcin : ∀ i, MapsTo (c i) source (T \ interior S))
    (houter : ∀ i z, z ∈ source → (c i z ∈ frontier T ↔ z.1 = 0))
    (hinner : ∀ i z, z ∈ source → (c i z ∈ frontier S ↔ z.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source))
    {f : P2 → X} {τ : C3 → X}
    (hf : PolyhedralPLInCharts e f (T \ interior S))
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : (T \ interior S) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    {U : Set X} (mark : Bool → Set X)
    (hfU : MapsTo f (T \ interior S) U) (hτU : MapsTo τ tube U)
    (hffront : ∀ x ∈ T \ interior S, f x ∈ frontier U ↔ x ∈ frontier T ∨ x ∈ frontier S)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier U ↔ z.2 = 0 ∨ z.2 = 1)
    (hfouter : ∀ x ∈ T \ interior S, x ∈ frontier T → f x ∈ mark false)
    (hfinner : ∀ x ∈ T \ interior S, x ∈ frontier S → f x ∈ mark true)
    (hτbottom : ∀ z ∈ tube, z.2 = 0 → τ z ∈ mark false)
    (hτtop : ∀ z ∈ tube, z.2 = 1 → τ z ∈ mark true)
    (M : SourceDoubleComponents e f (T \ interior S) (frontier T ∪ frontier S) U)
    (selected : Bool → M.Index) (hcenter : ∀ i, c i '' arm 0 = M.pieces (selected i))
    {R : Set Y} (projection : C(X, Y)) (hprojection : MapsTo projection U R)
    (rim : C(frontier T, R)) (hrim : ∀ z : frontier T, (rim z : Y) = projection (f z))
    (hnon : ¬ rim.Nullhomotopic) :
    ∃ (g : P2 → X) (original : C(Ann, R)),
      PolyhedralPLInCharts e g Ann ∧ (∀ z : Ann, (original z : Y) = projection (g z)) ∧
      MapsTo g Ann U ∧
      (∀ z ∈ Ann, g z ∈ frontier U ↔ depth 8 z = -1 ∨ depth 8 z = 1) ∧
      (∀ z ∈ Ann, depth 8 z = -1 → g z ∈ mark false) ∧
      (∀ z ∈ Ann, depth 8 z = 1 → g z ∈ mark true) ∧
      (∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic) ∧
      IsLocallyInjective (fun z : Ann ↦ g z) ∧
      IsCompact (doubleLocusOn g Ann) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → g x = g y → Nonempty (RawSourceCrossing e g Ann U x y)) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann, x ≠ y → x ≠ z → g x = g y → g x = g z → y = z) ∧
      Nonempty (SourceDoubleComponents e g Ann Rim U) ∧
      doubleBoundaryComponentCount g Ann Rim <
        doubleBoundaryComponentCount f (T \ interior S) (frontier T ∪ frontier S) ∧
      doubleInteriorComponentCount g Ann Rim ≤
        doubleInteriorComponentCount f (T \ interior S) (frontier T ∪ frontier S) := by
  obtain ⟨positive, E, H, p, g, C, hH, hpval, hES, hEdis, hcover, hcontact,
    hleft, hright, hg, hHo, hHi, hgU, hgfront, hg0, hg1, hdouble⟩ :=
    exists_original_spanning_resolution_exact_fibers hcompat hS hT hST c hcPL hci hcin
      houter hinner hdis hf hτ hτi h0 h1 hfull mark hfU hτU hffront hτfront
        hfouter hfinner hτbottom hτtop
  let sign (j : Fin 2) (i : Bool) := if j = 0 then positive i else !(positive i)
  have hcount := spanning_resolution_boundary_count_decrease c hcin hci hdis hτi h0 h1
    hfull houter E H sign hES hEdis hcover hcontact hHo hHi M.pieces M.mate
      M.literalPartner M.literal_cover M.compact M.connected M.disjoint M.literalPartner_value
        M.literalPartner_free M.literalPartner_unique M.literalPartner_component selected hcenter C hdouble
  have hQ : frontier T ⊆ T \ interior S := by
    intro x hx
    refine ⟨hT.isCompact.isClosed.frontier_subset hx, ?_⟩
    intro hxS
    exact disjoint_left.mp disjoint_interior_frontier (hST (interior_subset hxS)) hx
  have hprojf : ContinuousOn (projection ∘ f) (frontier T) :=
    projection.continuous.comp_continuousOn (hf.continuousOn.mono hQ)
  have hprojfR : MapsTo (projection ∘ f) (frontier T) R :=
    hprojection.comp (hfU.mono_left hQ)
  have hprojt : ContinuousOn (projection ∘ τ) tube :=
    projection.continuous.comp_continuousOn hτ.continuousOn
  have hprojtR : MapsTo (projection ∘ τ) tube R := hprojection.comp hτU
  obtain ⟨j, newrim, hnewrim, hnewnon⟩ := exists_essential_spanning_candidate hT hQ c
    (fun i ↦ (hcPL i).continuousOn) houter E hEdis hcover positive H hH hHo
      hcontact hleft hright (projection ∘ f) hprojf hprojfR rim hrim hnon
        (projection ∘ τ) hprojt hprojtR
        (fun z hz ↦ congrArg projection (h0 z hz))
        (fun z hz ↦ congrArg projection (h1 z hz))
        (fun j k ↦ projection ∘ (![f ∘ p j,
          (τ ∘ tubeArmOrientation (!(sign j false)) (!(sign j true))) ∘ resolvingSquare true] k))
        (fun j ↦ projection ∘ g j) (fun j ↦ (C j).map projection)
        (fun j z ↦ congrArg (projection ∘ f) (hpval j z).symm)
        (fun _ _ ↦ rfl)
        (fun j ↦ projection.continuous.comp_continuousOn (hg j).continuousOn)
        (fun j ↦ hprojection.comp (hgU j))
  let original : C(Ann, R) :=
    { toFun z := ⟨projection (g j z), hprojection (hgU j z.property)⟩
      continuous_toFun := (projection.continuous.comp (hg j).continuousOn.domRestrict).subtype_mk _ }
  have hessential : ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic :=
    planarAnnulusRims_nonnull_of_outer original newrim (fun z ↦ Subtype.ext (hnewrim z)) hnewnon
  have hclosed (k : Fin 2) : IsClosed (E k) := by
    let : CompactSpace Sq := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    let : CompactSpace (E k) := (H k).compactSpace
    exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hG : IsCompact (doubleLocusOn f (T \ interior S)) :=
    M.space ▸ M.graph.isCompact_space_of_finite M.finite
  have hord (a b : Fin 2) (hdisks : Disjoint (E a) (E b))
      (hcov : (c false '' source ∪ c true '' source) ∪ (E a ∪ E b) = T \ interior S) :=
    spanning_resolution_preserves_ordinary_crossings c (fun i ↦ (hcPL i).continuousOn)
      hcin hci hdis hτi h0 h1 hfull (H a) (hclosed b) (hES a) hdisks hcov
        (sign a) (hcontact a) (hleft a) (hright a) (C a)
        (fun z ↦ congrArg f (hpval a z).symm) (hdouble a)
        (hT.isCompact.diff isOpen_interior) hf.continuousOn (hg a).continuousOn hG
        M.literalPartner M.literalPartner.continuous
        (fun x ↦ (M.literalPartner_value x).symm) (fun x ↦ (M.literalPartner_free x).symm)
        M.literalPartner_unique (fun x hx y hy he hn ↦ M.crossings x hx y hy hn he)
  have hproper := hgfront j
  have hordinary : IsCompact (doubleLocusOn (g j) Ann) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann, g j x = g j y → g j x = g j z → x ≠ y → x ≠ z → y = z) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, g j x = g j y → x ≠ y → Nonempty (RawSourceCrossing e (g j) Ann U x y)) ∧
      IsLocallyInjective (fun z : Ann ↦ g j z) := by
    fin_cases j
    · exact hord 0 1 hEdis hcover
    · exact hord 1 0 hEdis.symm (by simpa only [union_comm (E 1) (E 0)] using hcover)
  obtain ⟨hcompact, hunique, hraw, hlocal⟩ := hordinary
  have hraw' := fun x hx y hy hn he ↦ hraw x hx y hy he hn
  have hunique' := fun x hx y hy z hz hn₁ hn₂ he₁ he₂ ↦ hunique x hx y hy z hz he₁ he₂ hn₁ hn₂
  have hcomponents : Nonempty (SourceDoubleComponents e (g j) Ann Rim U) := by
    obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
    have hh := nonempty_sourceDoubleComponents hcompat K hK Rim
      (hKs.symm ▸ hg j) (hKs.symm ▸ hgU j) (hKs.symm ▸ hcompact.isClosed)
      (hKs.symm ▸ hproper) (hKs.symm ▸ hraw') (hKs.symm ▸ hunique')
    exact hKs ▸ hh
  exact ⟨g j, original, hg j, fun _ ↦ rfl, hgU j, hproper, hg0 j, hg1 j,
    hessential, hlocal, hcompact, hraw', hunique', hcomponents, (hcount j).1, (hcount j).2⟩

end PoincareConjecture.M76.Dehn
