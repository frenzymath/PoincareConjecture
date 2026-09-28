import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripPeriod
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.NormalizedIdentityTube

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => Metric.closedBall (0 : V2) 1

def sourceTubeDiagonal (j : Fin 2) (u : ℝ) : P2 := (u, if j = 0 then u else -u)

theorem periodicTubeCoordinates_diagonal (L d a b s u : ℝ) (j : Fin 2) :
    periodicTubeCoordinates L d a b (sourceTubeDiagonal j u, s) =
      signedSheetStripMap j (sourceStripPeriodCoordinates L d a b (s, u)) := by
  fin_cases j <;> ext <;>
    simp [periodicTubeCoordinates_apply, sourceTubeDiagonal, signedSheetStripMap_apply,
      sourceStripPeriodCoordinates_apply, signedSquareToDiamond_apply, div_eq_inv_mul] <;> ring

theorem exists_signedSheetStripMap_eq {a b : ℝ} (j : Fin 2)
    (z : P2 × ℝ) (hz : z ∈ signedTubeDiamond ×ˢ Icc a b)
    (hs : z.1 ∈ signedTubeSheet j) :
    ∃ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b, signedSheetStripMap j x = z := by
  have hzero := (signedTubeSheet_coordinate_iff z.1 hz.1 j).mp hs
  have hbound := (signedTubeDiamond_coordinate_iff z.1).mp hz.1
  fin_cases j
  · have h0 : z.1.1 = 0 := hzero
    have hb : |z.1.2| ≤ 1 := by simpa [h0] using hbound
    refine ⟨(z.1.2, z.2), ⟨abs_le.mp hb, hz.2⟩, ?_⟩
    ext <;> simp [signedSheetStripMap_apply, h0]
  · have h0 : z.1.2 = 0 := hzero
    have hb : |z.1.1| ≤ 1 := by simpa [h0] using hbound
    refine ⟨(z.1.1, z.2), ⟨abs_le.mp hb, hz.2⟩, ?_⟩
    ext <;> simp [signedSheetStripMap_apply, h0]

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem OrdinaryIntervalMarkedModel.graph_injOn_clip (D : OrdinaryIntervalMarkedModel old i)
    (j : Fin 2) : InjOn (D.graph ∘ f) (D.clips j.castSucc).space := by
  intro x hx y hy hxy
  have hx' := (D.clips_data j.castSucc).2.1.subset hx
  have hy' := (D.clips_data j.castSucc).2.1.subset hy
  have heq := D.graph_separates (f x) hx'.2 (f y) hxy
  have hinj : Topology.IsEmbedding (fun z : (D.source j.castSucc).space => f z) := by
    fin_cases j
    · exact D.left_embedding
    · exact D.right_embedding
  exact congrArg Subtype.val (hinj.injective (a₁ := ⟨x, hx'.1⟩)
    (a₂ := ⟨y, hy'.1⟩) heq)

theorem OrdinaryIntervalMarkedModel.source_tube_preimage
    (D : OrdinaryIntervalMarkedModel old i) {a b : ℝ}
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (hK : MapsTo sigma (signedTubeDiamond ×ˢ Icc a b) D.complex.space)
    (hsheet : ∀ (j : Fin 2) (z : ↥(signedTubeDiamond ×ˢ Icc a b)),
      sigma z ∈ (D.marks (.inr j.castSucc)).space ↔ z.1.1 ∈ signedTubeSheet j)
    (phi : Fin 2 → P2 → V2)
    (hclip : ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      phi j x ∈ (D.clips j.castSucc).space)
    (hvalue : ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      f (phi j x) = (D.inverse (sigma (signedSheetStripMap j x)) : X))
    (hgraph : ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      D.graph (f (phi j x)) = sigma (signedSheetStripMap j x)) :
    D2 ∩ f ⁻¹' ((fun z => (D.inverse (sigma z) : X)) ''
      (signedTubeDiamond ×ˢ Icc a b)) =
      (phi 0 '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) ∪
        (phi 1 '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) := by
  ext x
  constructor
  · rintro ⟨hxD, z, hz, hzx⟩
    have hxcore : f x ∈ D.core := hzx ▸ (D.inverse (sigma z)).property
    have hxclips : x ∈ (D.clips 0).space ∪ (D.clips 1).space :=
      D.complete_core_preimage.subset ⟨hxD, hxcore⟩
    have hex : ∃ j : Fin 2, x ∈ (D.clips j.castSucc).space := by
      rcases hxclips with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨j, hx⟩ := hex
    have hgx : D.graph (f x) = sigma z :=
      (congrArg D.graph hzx.symm).trans (D.graph_inverse _ (hK hz))
    have hzmark : sigma z ∈ (D.marks (.inr j.castSucc)).space := by
      exact hgx ▸ (D.clips_data j.castSucc).2.2.2.subset ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hwz⟩ := exists_signedSheetStripMap_eq j z hz
      ((hsheet j ⟨z, hz⟩).mp hzmark)
    have hwx : phi j w = x := D.graph_injOn_clip j (hclip j w hw) hx
      ((hgraph j w hw).trans ((congrArg sigma hwz).trans hgx.symm))
    have hximage : x ∈ phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := ⟨w, hw, hwx⟩
    fin_cases j
    · exact Or.inl hximage
    · exact Or.inr hximage
  · have hmem (j : Fin 2) : phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b) ⊆
        D2 ∩ f ⁻¹' ((fun z => (D.inverse (sigma z) : X)) ''
          (signedTubeDiamond ×ˢ Icc a b)) := by
      rintro _ ⟨w, hw, rfl⟩
      have hwsource := ((D.clips_data j.castSucc).2.1.subset (hclip j w hw)).1
      exact ⟨D.source_subset j.castSucc hwsource, signedSheetStripMap j w,
        signedSheetStripMap_mem j hw, (hvalue j w hw).symm⟩
    exact fun hx => hx.elim (fun h => hmem 0 h) (fun h => hmem 1 h)

theorem OrdinaryIntervalMarkedModel.source_circle_subset_strip_image
    (D : OrdinaryIntervalMarkedModel old i) {a b : ℝ}
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (haxisImage : (fun t => sigma ((0, 0), t)) '' Icc a b = (D.marks (.inr 2)).space)
    (phi : Fin 2 → P2 → V2)
    (hclip : ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      phi j x ∈ (D.clips j.castSucc).space)
    (hgraph : ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      D.graph (f (phi j x)) = sigma (signedSheetStripMap j x))
    (j : Fin 2) :
    old.pieces (if j = 0 then i else old.mate i) ⊆
      phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
  intro x hx
  have himage : f '' old.pieces (if j = 0 then i else old.mate i) =
      f '' old.pieces i := by
    fin_cases j
    · rfl
    · exact old.piece_image_mate i
  have hsource : x ∈ (D.source j.castSucc).space := by
    fin_cases j
    · exact D.left_contains hx
    · exact D.right_contains hx
  have hximage : f x ∈ f '' old.pieces i := himage.subset (mem_image_of_mem f hx)
  have hxcore : f x ∈ D.core := interior_subset (D.core_neighborhood hximage)
  have hxclip : x ∈ (D.clips j.castSucc).space :=
    (D.clips_data j.castSucc).2.1.symm.subset ⟨hsource, hxcore⟩
  have hmark : D.graph (f x) ∈ (D.marks (.inr 2)).space := by
    apply (D.marks_image 2).symm.subset
    refine ⟨f x, ⟨hxcore, ?_⟩, rfl⟩
    rwa [D.selected_source]
  obtain ⟨t, ht, htx⟩ := haxisImage.symm.subset hmark
  have h0t : (0, t) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b := ⟨by norm_num, ht⟩
  have hstrip : signedSheetStripMap j (0, t) = ((0, 0), t) := by
    fin_cases j <;> simp [signedSheetStripMap_apply]
  refine ⟨(0, t), h0t, D.graph_injOn_clip j (hclip j _ h0t) hxclip ?_⟩
  exact (hgraph j _ h0t).trans ((congrArg sigma hstrip).trans htx)

theorem OrdinaryIntervalMarkedModel.exists_paired_source_annuli
    (D : OrdinaryIntervalMarkedModel old i) {a b L d : ℝ}
    (hab : a < b) (hd : 0 < d) (hwidth : 4 * d < L)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3)) (closing : Fin 2 → Bool)
    (hPL : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc a b))
    (hK : MapsTo sigma (signedTubeDiamond ×ˢ Icc a b) D.complex.space)
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          signedTubeReflection closing (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          signedTubeReflection closing (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (n : Fin 2 → ℕ) (P : ∀ j, Polygon V2 (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hinjP : ∀ j, Function.Injective (P j))
    (hboundary : ∀ j, (P j).boundary ℝ = old.pieces (if j = 0 then i else old.mate i))
    (hsheet : ∀ (j : Fin 2) (x : ↥(signedTubeDiamond ×ˢ Icc a b)),
      sigma x ∈ (D.marks (.inr j.castSucc)).space ↔
        (x : P2 × ℝ).1 ∈ signedTubeSheet j)
    (haxis : ∀ x : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x ∈ (D.marks (.inr 2)).space ↔ (x : P2 × ℝ).1 = (0, 0))
    (haxisImage : (fun t => sigma ((0, 0), t)) '' Icc a b = (D.marks (.inr 2)).space) :
    ∃ (A : Fin 2 → Set V2) (c : ∀ j, squareAnnulus L d ≃ₜ A j),
      (∀ j, closing j = true) ∧
      (∀ j, (c j).IsFinitePL ∧ (c j).symm.IsFinitePL) ∧
      (∀ j, A j ⊆ (D.clips j.castSucc).space) ∧ Disjoint (A 0) (A 1) ∧
      (∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        f (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩) =
        (D.inverse (sigma (periodicTubeCoordinates L d a b
          (sourceTubeDiagonal j u, s))) : X)) ∧
      (∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        D.graph (f (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩)) =
        sigma (periodicTubeCoordinates L d a b (sourceTubeDiagonal j u, s))) ∧
      (∀ j (p : squareAnnulus L d), (c j p : V2) ∈ (P j).boundary ℝ ↔ depth L p = 0) ∧
      (∀ j, (fun p : squareAnnulus L d => (c j p : V2)) '' {p | depth L p = 0} =
        (P j).boundary ℝ) ∧
      D2 ∩ f ⁻¹' ((fun z => (D.inverse (sigma (periodicTubeCoordinates L d a b z)) : X)) ''
        _root_.Dehn.identityTube L d) = A 0 ∪ A 1 := by
  classical
  have hL : 0 < L := by linarith
  obtain ⟨phi, hclosing, hphiPL, hclip, hvalue, hgraph, hmiddle, hphiFib⟩ :=
    D.exists_paired_source_strips hab sigma closing hPL hfib n P hP hinjP
      hboundary hsheet haxis
  choose c hc hci hcperiod using fun j =>
    exists_source_annulus_of_endpoint_strip hd hwidth hab (phi j) (hphiPL j) (hphiFib j)
  let A : Fin 2 → Set V2 := fun j => phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)
  have hAsub (j : Fin 2) : A j ⊆ (D.clips j.castSucc).space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hclip j x hx
  have hsource (j : Fin 2) : A j ⊆ (D.source j.castSucc).space :=
    fun _ hx => ((D.clips_data j.castSucc).2.1.subset (hAsub j hx)).1
  have hdis : Disjoint (A 0) (A 1) := D.disjoint.mono (hsource 0) (hsource 1)
  have hcval (j : Fin 2) (p : squareAnnulus L d) (s : ℝ) (hs : s ∈ Icc 0 (4 * L))
      (hp : (p : P2) = annulusMap L hL ((s : AddCircle (4 * L)), depth L p)) :
      (c j p : V2) = phi j (sourceStripPeriodCoordinates L d a b (s, depth L p)) := by
    have hu : depth L p ∈ Icc (-d) d := mem_squareAnnulus_iff_depth.mp p.property
    have heq : p = ⟨annulusMap L hL ((s : AddCircle (4 * L)), depth L p),
        _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨depth L p, hu⟩⟩ := Subtype.ext hp
    calc
      (c j p : V2) = c j ⟨annulusMap L hL ((s : AddCircle (4 * L)), depth L p),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨depth L p, hu⟩⟩ :=
        congrArg (fun q => (c j q : V2)) heq
      _ = phi j (depth L p / d, a + ((b - a) / (4 * L)) * s) := hcperiod j s hs ⟨_, hu⟩
      _ = _ := congrArg (phi j)
        (sourceStripPeriodCoordinates_apply L d a b (s, depth L p)).symm
  have htrace (j : Fin 2) (p : squareAnnulus L d) :
      (c j p : V2) ∈ (P j).boundary ℝ ↔ depth L p = 0 := by
    obtain ⟨s, hs, hp⟩ := exists_period_parameter_of_depth hd hwidth p
    have hu := mem_squareAnnulus_iff_depth.mp p.property
    rw [hcval j p s hs hp, hmiddle j _
      (sourceStripPeriodCoordinates_mapsTo hL hd hab ⟨hs, hu⟩),
      sourceStripPeriodCoordinates_apply]
    simp [div_eq_zero_iff, hd.ne']
  refine ⟨A, c, hclosing, fun j => ⟨hc j, hci j⟩, hAsub, hdis, ?_, ?_, htrace, ?_, ?_⟩
  · intro j s hs u
    rw [hcperiod j s hs u, periodicTubeCoordinates_diagonal]
    have hx := sourceStripPeriodCoordinates_mapsTo hL hd hab (show
      (s, (u : ℝ)) ∈ rectangle (4 * L) d from ⟨hs, u.property⟩)
    simpa only [sourceStripPeriodCoordinates_apply] using hvalue j _ hx
  · intro j s hs u
    rw [hcperiod j s hs u, periodicTubeCoordinates_diagonal]
    have hx := sourceStripPeriodCoordinates_mapsTo hL hd hab (show
      (s, (u : ℝ)) ∈ rectangle (4 * L) d from ⟨hs, u.property⟩)
    simpa only [sourceStripPeriodCoordinates_apply] using hgraph j _ hx
  · intro j
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (htrace j p).mpr hp
    · intro hx
      have hxA : x ∈ A j := D.source_circle_subset_strip_image sigma haxisImage
        phi hclip hgraph j ((hboundary j).subset hx)
      refine ⟨(c j).symm ⟨x, hxA⟩, ?_, ?_⟩
      · apply (htrace j _).mp
        simpa only [Homeomorph.apply_symm_apply] using hx
      · exact congrArg Subtype.val ((c j).apply_symm_apply _)
  · have himage : (fun z => (D.inverse (sigma (periodicTubeCoordinates L d a b z)) : X)) ''
        _root_.Dehn.identityTube L d =
        (fun z => (D.inverse (sigma z) : X)) '' (signedTubeDiamond ×ˢ Icc a b) := by
      change ((fun z => (D.inverse (sigma z) : X)) ∘ periodicTubeCoordinates L d a b) '' _ = _
      rw [image_comp, periodicTubeCoordinates_image hL hd hab]
    rw [himage]
    exact D.source_tube_preimage sigma hK hsheet phi hclip hvalue hgraph

end PoincareConjecture.M76.Dehn
