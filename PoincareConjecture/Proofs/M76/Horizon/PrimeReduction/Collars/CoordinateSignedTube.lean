import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcTubeMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.SelectedChartStars
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

private theorem coordinate_identity_pl
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {f : V3 → V3} (hf : EqOn f id K.space) :
    PolyhedralPLInCharts (fun _ : Unit => OpenPartialHomeomorph.refl V3) f K.space := by
  refine ⟨continuousOn_id.congr hf, ?_⟩
  intro x
  refine ⟨(), K, univ, hK, Subset.rfl, isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · intro z hz
    exact mem_univ _
  · apply ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK).congr
    intro z hz
    exact (hf hz).symm

open Classical in




theorem exists_coordinate_signed_tube
    {κ : Type*} [Finite κ]
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {R A : Set V3} {a b : V3} (hd : IsFinitePLBallPair ℝ A {a, b}) (hab : a ≠ b)
    (hAK : A ⊆ interior K.space) (hAR : A ⊆ R)
    (hAF : A ∩ frontier R = {a, b})
    (S : Fin 2 → Set V3) (M : κ → SimplicialComplex ℝ V3)
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : (M reg).space = K.space ∩ R)
    (hfr : (M fr).space = K.space ∩ frontier R)
    (harc : (M arc).space = A)
    (hsheet : ∀ i, (M (sheet i)).space = K.space ∩ S i)
    (hcharts : ∀ x ∈ A, ∃ B : OpenPartialHomeomorph V3 V3,
      x ∈ B.source ∧ B ∈ piecewiseAffineGroupoid V3 ∧
      (∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0) ∧
      (∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0)) ∧
      (B.source ⊆ interior R ∨
        (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
        ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)) :
    ∃ (N : SimplicialComplex ℝ V3) (L : κ → SimplicialComplex ℝ V3)
      (hN : N.faces.Finite)
      (hL : ∀ j, L j ≤ N ∧ (L j).space = (M j).space ∧
        ∀ f ∈ N.faces, (∀ v ∈ f, v ∈ (L j).vertices) → f ∈ (L j).faces),
      N.IsSubdivision K ∧
      letI : Fintype N.faces := hN.fintype
      letI : ∀ i, Fintype (L i).faces := fun i => (hN.subset (hL i).1).fintype
      ∃ (bArc : I ≃ₜ (L arc).space)
        (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ ((L reg).barycentricNeighborhood (L arc)).space),
        bArc.IsFinitePL ∧
        (bArc ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3) = a ∧
        (bArc ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3) = b ∧
        tube.IsFinitePL ∧
        (∀ t : I, (tube ⟨((0, 0), t), Dehn.signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ : V3) = bArc t) ∧
        (∀ i (x : ↥(Dehn.signedTubeDiamond ×ˢ I)),
          (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet i ↔ (tube x : V3) ∈ S i) ∧
        ∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
          (tube x : V3) ∈ frontier R ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1 := by
  classical
  let : DecidableEq V3 := Classical.decEq V3
  let e := fun _ : Unit => OpenPartialHomeomorph.refl V3
  have he (i j : Unit) : (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using
      (piecewiseAffineGroupoid V3).id_mem
  have hcover (x : V3) : ∃ i, x ∈ (e i).source := ⟨(), mem_univ x⟩
  have hid : PolyhedralPLInCharts e id K.space := coordinate_identity_pl K hK (fun _ _ => rfl)
  choose G hpG hGPL hGA hGS hGR using hcharts
  let charts : ↥(K.space ∩ id ⁻¹' A) → OpenPartialHomeomorph V3 V3 :=
    fun x => G x x.property.2
  have hcompat (x : ↥(K.space ∩ id ⁻¹' A)) (i : Unit) :
      (e i).symm.trans (charts x) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using
      hGPL x x.property.2
  have hmark : (M arc).space = K.space ∩ id ⁻¹' A := by
    rw [harc]
    exact (inter_eq_right.mpr (fun x hx => interior_subset (hAK hx))).symm
  obtain ⟨N, L, hN, hNK, hL, hstars⟩ :=
    Dehn.exists_selected_compatible_chart_stars e he hcover K hK hid hd.isCompact.isClosed
      charts hcompat (fun x => hpG x x.property.2) M
      (fun i => hK.subset (hMK i)) (fun i => space_subset_of_le (hMK i)) arc hmark
  have hLs : (L arc).space = A := (hL arc).2.1.trans harc
  obtain ⟨bArc, hbArc, hb0, hb1⟩ :=
    (show IsFinitePLBallPair ℝ (L arc).space {a, b} from hLs.symm ▸ hd).exists_unitInterval_chart_with_endpoints hab
  have haN : a ∈ N.space := hb0 ▸ space_subset_of_le (hL arc).1 (bArc ⟨0, ⟨le_rfl, zero_le_one⟩⟩).property
  let g : V3 → N.space := fun x => if hx : x ∈ N.space then ⟨x, hx⟩ else ⟨a, haN⟩
  have hg (x : V3) (hx : x ∈ N.space) : (g x : V3) = x := by simp only [g, dif_pos hx]
  have hgPL : PolyhedralPLInCharts e (fun x => (g x : V3)) N.space :=
    coordinate_identity_pl N hN hg
  have hLg (i : κ) (x : V3) (hx : x ∈ N.space) :
      x ∈ (L i).space ↔ (g x : V3) ∈ (M i).space := by rw [hg x hx, (hL i).2.1]
  have hreg' (x : V3) (hx : x ∈ N.space) : x ∈ (L reg).space ↔ (g x : V3) ∈ R := by
    rw [hLg reg x hx, hreg, mem_inter_iff, hg x hx]
    exact and_iff_right (hNK.space_eq.subset hx)
  have hfr' (x : V3) (hx : x ∈ N.space) : x ∈ (L fr).space ↔ (g x : V3) ∈ frontier R := by
    rw [hLg fr x hx, hfr, mem_inter_iff, hg x hx]
    exact and_iff_right (hNK.space_eq.subset hx)
  have harc' (x : V3) (hx : x ∈ N.space) : x ∈ (L arc).space ↔ (g x : V3) ∈ A := by
    rw [hLg arc x hx, harc]
  have hsheet' (i : Fin 2) (x : V3) (hx : x ∈ N.space) :
      x ∈ (L (sheet i)).space ↔ (g x : V3) ∈ S i := by
    rw [hLg (sheet i) x hx, hsheet, mem_inter_iff, hg x hx]
    exact and_iff_right (hNK.space_eq.subset hx)
  choose q hmaps haff using fun p : (L arc).vertices => hstars p p.property
  let B : (L arc).vertices → OpenPartialHomeomorph V3 V3 := fun p => charts (q p)
  have hB (p : (L arc).vertices) :
      MapsTo (fun z => (g z : V3)) (N.closedStar p).space (B p).source ∧
      (N.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0) := by
    have hstar : (N.closedStar p).space ⊆ N.space :=
      space_subset_of_le (fun _ hs => hs.1)
    refine ⟨?_, ?_, hGA (q p) (q p).property.2, hGS (q p) (q p).property.2⟩
    · intro x hx
      change (g x : V3) ∈ (B p).source
      rw [hg x (hstar hx)]
      exact hmaps p hx
    · apply (haff p).congr
      intro x hx
      exact congrArg (B p) (hg x (hstar hx)).symm
  have hregion (p : (L arc).vertices) := hGR (q p) (q p).property.2
  have hcontact : (L arc).space ∩ (L fr).space =
      {(bArc ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3), (bArc ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3)} := by
    rw [hb0, hb1, hLs, (hL fr).2.1, hfr, ← inter_assoc,
      inter_eq_left.mpr (fun x hx => interior_subset (hAK hx)), hAF]
  let : Fintype N.faces := hN.fintype
  let : ∀ i, Fintype (L i).faces := fun i => (hN.subset (hL i).1).fintype
  obtain ⟨tube, htube, haxis, hsheets, hends⟩ := Dehn.exists_original_signed_tube_map
    (show A ⊆ interior N.space by simpa only [hNK.space_eq] using hAK) hAR
    (hAF ▸ (finite_singleton b).insert a) S N id continuous_id (Homeomorph.refl N.space)
    (fun _ => rfl) g (fun z => hg z z.property) hgPL L
    (fun i => (hL i).1) (fun i => (hL i).2.2) reg fr arc sheet
    hreg' hfr' harc' hsheet' B hB hregion bArc hbArc hcontact
  have htN (x : ↥(Dehn.signedTubeDiamond ×ˢ I)) : (tube x : V3) ∈ N.space :=
    space_subset_of_le (hL reg).1
      ((L reg).barycentricSubdivision_isSubdivision.space_eq.subset
        (space_subset_of_le ((L reg).barycentricNeighborhood_le (L arc)) (tube x).property))
  refine ⟨N, L, hN, hL, hNK, bArc, tube, hbArc, hb0, hb1, htube, haxis, ?_, ?_⟩
  · intro i x
    exact (hsheets i x).trans ((hsheet' i (tube x) (htN x)).trans (by rw [hg _ (htN x)]))
  · intro x
    rw [← hg (tube x) (htN x), ← hfr' (tube x) (htN x)]
    exact hends x

end PoincareConjecture.M76
