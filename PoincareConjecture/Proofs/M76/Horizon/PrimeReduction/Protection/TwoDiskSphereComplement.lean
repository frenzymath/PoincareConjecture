import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.NestedDiskAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.FinitePLBallCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Collars.FinitePLBallBoundaryCollar










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_two_disk_sphere_complement_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S : Set E} (hB : IsFinitePLBallPair V3 B S)
    (d r : Bool → Set E) (hd : ∀ i, IsFinitePLBallPair P2 (d i) (r i))
    (hdS : ∀ i, d i ⊆ S) (hdis : Disjoint (d false) (d true)) :
    ∃ H : Ann ≃ₜ (S \ ((d false \ r false) ∪ (d true \ r true)) : Set E),
      H.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (H z : E) ∈ r false) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (H z : E) ∈ r true) ∧
      ((S \ ((d false \ r false) ∪ (d true \ r true))) ∩
        (d false ∪ d true) = r false ∪ r true) := by
  have htrueNe : (d true).Nonempty := (hd true).sdiff_nonempty.mono sdiff_subset
  have hout : (S \ d false).Nonempty := by
    obtain ⟨x, hx⟩ := htrueNe
    exact ⟨x, hdS true hx, fun h => disjoint_left.mp hdis h hx⟩
  have houter := hB.boundary_disk_complement (by simp) (hd false) (hdS false) hout
  have hinner : d true ⊆ (S \ (d false \ r false)) \ r false := by
    intro x hx
    have hn : x ∉ d false := fun h => disjoint_left.mp hdis h hx
    exact ⟨⟨hdS true hx, fun h => hn h.1⟩, fun h => hn ((hd false).1 h)⟩
  obtain ⟨H, hH, hzero, hone⟩ :=
    Dehn.exists_square_annulus_nested_ball_pairs (hd true) houter hinner
  have heq : (S \ (d false \ r false)) \ (d true \ r true) =
      S \ ((d false \ r false) ∪ (d true \ r true)) := by
    ext x
    simp only [mem_sdiff, mem_union, not_or]
    tauto
  refine ⟨H.trans (Homeomorph.setCongr heq), hH.setCongr rfl heq,
    hzero, hone, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨_, hx⟩, hxfalse | hxtrue⟩
    · exact Or.inl (by by_contra hn; exact hx (Or.inl ⟨hxfalse, hn⟩))
    · exact Or.inr (by by_contra hn; exact hx (Or.inr ⟨hxtrue, hn⟩))
  · rintro (hx | hx)
    · have hd0 := (hd false).1 hx
      refine ⟨⟨hdS false hd0, ?_⟩, Or.inl hd0⟩
      rintro (h | h)
      · exact h.2 hx
      · exact disjoint_left.mp hdis hd0 h.1
    · have hd1 := (hd true).1 hx
      refine ⟨⟨hdS true hd1, ?_⟩, Or.inr hd1⟩
      rintro (h | h)
      · exact disjoint_left.mp hdis h.1 hd1
      · exact h.2 hx

theorem exists_two_disk_sphere_complement_annulus_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S : Set E} (hB : IsFinitePLBallPair V3 B S)
    (d r : Bool → Set E) (hd : ∀ i, IsFinitePLBallPair P2 (d i) (r i))
    (hdS : ∀ i, d i ⊆ S) (hdis : Disjoint (d false) (d true)) :
    ∃ (H : Ann ≃ₜ (S \ ((d false \ r false) ∪ (d true \ r true)) : Set E))
      (C : P2 × ℝ → E),
      H.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (H z : E) ∈ r false) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (H z : E) ∈ r true) ∧
      FinitePiecewiseAffineOn C (Ann ×ˢ I) ∧ InjOn C (Ann ×ˢ I) ∧
      MapsTo C (Ann ×ˢ I) B ∧
      (∀ z : Ann, C (z, 0) = H z) ∧
      (∀ z ∈ Ann ×ˢ I, C z ∈ S ↔ z.2 = 0) ∧
      (C '' (Ann ×ˢ I)) ∩ (d false ∪ d true) = r false ∪ r true ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : B → E) ⁻¹'
            (C '' ((Ann \ {z | depth 8 z = -1 ∨ depth 8 z = 1}) ×ˢ Ico 0 ε))) := by
  obtain ⟨H, hH, hzero, hone, hinter⟩ :=
    exists_two_disk_sphere_complement_annulus hB d r hd hdS hdis
  obtain ⟨c, HC, hHC, hHCval, hcin, hcbase, hcfront, δ, hδ, hδsmall, hopen⟩ :=
    hB.exists_finitePL_boundary_collar
  have hc : FinitePiecewiseAffineOn c (S ×ˢ I) := by
    obtain ⟨c0, hc0, hc0val⟩ := hHC
    exact hc0.congr (fun z hz => (hc0val ⟨z, hz⟩).symm.trans (hHCval ⟨z, hz⟩))
  have hci : InjOn c (S ×ˢ I) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (HC.injective (Subtype.ext
      ((hHCval ⟨x, hx⟩).trans (hxy.trans (hHCval ⟨y, hy⟩).symm))))
  have hHcopy := hH
  obtain ⟨f, hf, hfval⟩ := hHcopy
  have hfS (z : P2) (hz : z ∈ Ann) : f z ∈ S := by
    rw [← hfval ⟨z, hz⟩]
    exact (H ⟨z, hz⟩).property.1
  have hfi : InjOn f Ann := by
    intro x hx y hy hxy
    apply Subtype.mk.inj
    apply H.injective
    apply Subtype.ext
    exact (hfval ⟨x, hx⟩).trans (hxy.trans (hfval ⟨y, hy⟩).symm)
  have hfcopy := hf
  obtain ⟨K, hK, hKs, _⟩ := hfcopy
  obtain ⟨J, _, hJ, hJs, _, _⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).exists_finite_carrier_and_rim_complexes
  obtain ⟨P, hP, hPs, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  have hPspace : P.space = Ann ×ˢ I := by simpa only [hKs, hJs] using hPs
  have hfst : FinitePiecewiseAffineOn (Prod.fst : P2 × ℝ → P2) P.space :=
    (P.affineOnFaces_affine (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hP
  have hsnd : FinitePiecewiseAffineOn (Prod.snd : P2 × ℝ → ℝ) P.space :=
    (P.affineOnFaces_affine (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hP
  have hfprod : FinitePiecewiseAffineOn (fun z : P2 × ℝ => f z.1) P.space :=
    hf.comp hfst (fun _ hz => (hPspace.subset hz).1)
  let a : P2 × ℝ → E × ℝ := fun z => (f z.1, z.2)
  have ha : FinitePiecewiseAffineOn a (Ann ×ˢ I) := hPspace ▸ hfprod.prod_mk hsnd
  have haS : MapsTo a (Ann ×ˢ I) (S ×ˢ I) := fun z hz => ⟨hfS z.1 hz.1, hz.2⟩
  let C := c ∘ a
  have hCbase (z : Ann) : C (z, 0) = H z :=
    (hcbase (f z) (hfS z z.property)).trans (hfval z).symm
  have hCfront (z : P2 × ℝ) (hz : z ∈ Ann ×ˢ I) : C z ∈ S ↔ z.2 = 0 :=
    hcfront (a z) (haS hz)
  refine ⟨H, C, hH, hzero, hone, hc.comp ha haS, ?_,
    fun z hz => hcin (haS hz), hCbase, hCfront, ?_, δ, hδ, hδsmall, ?_⟩
  · intro z hz w hw hzw
    have heq := hci (haS hz) (haS hw) hzw
    have hsecond : z.2 = w.2 := congrArg (Prod.snd : E × ℝ → ℝ) heq
    exact Prod.ext (hfi hz.1 hw.1 (congrArg Prod.fst heq)) hsecond
  · ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hx⟩
      have hCS : C z ∈ S := hx.elim (fun h => hdS false h) (fun h => hdS true h)
      have ht := (hCfront z hz).mp hCS
      have hbase : C z = (H ⟨z.1, hz.1⟩ : E) := by
        calc
          C z = C (z.1, 0) := congrArg C (show z = (z.1, 0) from Prod.ext rfl ht)
          _ = (H ⟨z.1, hz.1⟩ : E) := hCbase ⟨z.1, hz.1⟩
      apply hinter.subset
      exact ⟨hbase.symm ▸ (H ⟨z.1, hz.1⟩).property, hx⟩
    · intro hx
      have hx' := hinter.symm.subset hx
      obtain ⟨z, hz⟩ := H.surjective ⟨x, hx'.1⟩
      refine ⟨⟨(z, 0), ⟨z.property, by simp⟩, ?_⟩, hx'.2⟩
      exact (hCbase z).trans (congrArg Subtype.val hz)
  · intro ε hε hεδ
    let T := d false ∪ d true
    have hTS : T ⊆ S := union_subset (hdS false) (hdS true)
    have hTcompact : IsCompact T := (hd false).isCompact.union (hd true).isCompact
    have hbad : IsClosed (c '' (T ×ˢ I)) :=
      ((hTcompact.prod isCompact_Icc).image_of_continuousOn
        (hc.continuousOn.mono (prod_mono hTS subset_rfl))).isClosed
    have hband (z : P2) (hz : z ∈ Ann) :
        f z ∉ T ↔ ¬ (depth 8 z = -1 ∨ depth 8 z = 1) := by
      have hr : f z ∈ T ↔ f z ∈ r false ∪ r true := by
        rw [← hinter]
        have hzH := (H ⟨z, hz⟩).property
        rw [hfval] at hzH
        exact ⟨fun h => ⟨hzH, h⟩, fun h => h.2⟩
      rw [hr, mem_union, ← hfval ⟨z, hz⟩, ← hzero ⟨z, hz⟩, ← hone ⟨z, hz⟩]
    have htime : Ico (0 : ℝ) ε ⊆ I := by
      intro t ht
      exact ⟨ht.1, le_trans (le_of_lt ht.2) (by linarith)⟩
    have heq : C '' ((Ann \ {z | depth 8 z = -1 ∨ depth 8 z = 1}) ×ˢ Ico 0 ε) =
        (c '' (S ×ˢ Ico 0 ε)) \ (c '' (T ×ˢ I)) := by
      apply Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        refine ⟨⟨a z, ⟨hfS z.1 hz.1.1, hz.2⟩, rfl⟩, ?_⟩
        rintro ⟨w, hw, he⟩
        have haa := hci (prod_mono hTS subset_rfl hw)
          (haS ⟨hz.1.1, htime hz.2⟩) he
        have heqfst : w.1 = f z.1 := congrArg Prod.fst haa
        have hfT : f z.1 ∈ T := heqfst ▸ hw.1
        exact ((hband z.1 hz.1.1).mpr hz.1.2) hfT
      · rintro y ⟨⟨w, hw, rfl⟩, hnot⟩
        have hwT : w.1 ∉ T := fun h =>
          hnot ⟨w, ⟨h, htime hw.2⟩, rfl⟩
        have hwA : w.1 ∈ S \ ((d false \ r false) ∪ (d true \ r true)) :=
          ⟨hw.1, fun h => hwT (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))⟩
        obtain ⟨z, hz⟩ := H.surjective ⟨w.1, hwA⟩
        have hfz : f z = w.1 := (hfval z).symm.trans (congrArg Subtype.val hz)
        have hdepth : ¬ (depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) :=
          (hband z z.property).mp (hfz.symm ▸ hwT)
        refine ⟨((z : P2), w.2), ⟨⟨z.property, hdepth⟩, hw.2⟩, ?_⟩
        change c (f z, w.2) = c w
        rw [hfz]
    rw [heq, preimage_sdiff]
    exact (hopen ε hε hεδ).sdiff (hbad.preimage continuous_subtype_val)

end PoincareConjecture.M76
