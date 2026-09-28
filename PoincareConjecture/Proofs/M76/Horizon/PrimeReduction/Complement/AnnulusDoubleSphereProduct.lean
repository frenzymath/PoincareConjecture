import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.AnnularBallProduct
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels

set_option autoImplicit false
open Set Geometry TriangularRoofModel

namespace Set

local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finitePL_sphere_product_of_annulus_double
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (B : Bool → Set E) (caps : Bool → Bool → Set E) (q : Bool → Set E)
    {band : Set E}
    (hB : ∀ b, IsFinitePLBallPair M (B b) (band ∪ (caps b false ∪ caps b true)))
    (hcaps : ∀ b s, IsFinitePLBallPair P2 (caps b s) (q s))
    (hmeet : ∀ b s, caps b s ∩ band = q s)
    (hdis : ∀ b, Disjoint (caps b true) (caps b false))
    (hcontact : B false ∩ B true = band)
    (e : band ≃ₜ (q false ×ˢ I : Set (E × ℝ))) (he : e.IsFinitePL)
    (hmem : ∀ s (x : band), (x : E) ∈ q s ↔
      (e x : E × ℝ) ∈ q false ×ˢ {if s then (1 : ℝ) else 0}) :
    ∃ H : (B false ∪ B true : Set E) ≃ₜ
        (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), H.IsFinitePL ∧
      ∀ s (x : (B false ∪ B true : Set E)),
        (x : E) ∈ caps false s ∪ caps true s ↔
          (H x : P3 × ℝ).2 = if s then (1 : ℝ) else 0 := by
  have hcapB (b s : Bool) : caps b s ⊆ B b := by
    apply subset_trans _ (hB b).1
    cases s
    · exact subset_union_left.trans subset_union_right
    · exact subset_union_right.trans subset_union_right
  have hbase : caps false false ∩ caps true false = q false := by
    apply Subset.antisymm
    · intro x hx
      exact (hmeet false false).subset ⟨hx.1,hcontact.subset
        ⟨hcapB false false hx.1,hcapB true false hx.2⟩⟩
    · exact fun _ hx => ⟨(hcaps false false).1 hx,(hcaps true false).1 hx⟩
  have hproducts (b : Bool) := (hB b).exists_product_extending_annulus
    (caps b) q (hcaps b) (hmeet b) (hdis b) e he hmem
  choose F hF hkeep hcapsF hbandF using hproducts
  let P := fun b => caps b false ×ˢ I
  have hPinter : P false ∩ P true = q false ×ˢ I := by
    ext z
    change ((z.1 ∈ caps false false ∧ z.2 ∈ I) ∧
      z.1 ∈ caps true false ∧ z.2 ∈ I) ↔ z.1 ∈ q false ∧ z.2 ∈ I
    constructor
    · exact fun hz => ⟨hbase.subset ⟨hz.1.1,hz.2.1⟩,hz.1.2⟩
    · exact fun hz => ⟨⟨(hbase.symm.subset hz.1).1,hz.2⟩,
        (hbase.symm.subset hz.1).2,hz.2⟩
  have hoverlap (x : B false) : (x : E) ∈ B true ↔ (F false x : E × ℝ) ∈ P true := by
    constructor
    · intro hx
      have hb := (hbandF false x).mp (hcontact.subset ⟨x.property,hx⟩)
      exact ⟨(hcaps true false).1 hb.1,hb.2⟩
    · intro hx
      have hb := (hbandF false x).mpr (hPinter.subset ⟨(F false x).property,hx⟩)
      exact (hcontact.symm.subset hb).2
  have hagree (x : E) (hx : x ∈ B false) (hy : x ∈ B true) :
      (F false ⟨x,hx⟩ : E × ℝ) = F true ⟨x,hy⟩ := by
    have hb := hcontact.subset ⟨hx,hy⟩
    exact (hkeep false ⟨x,hb⟩).trans (hkeep true ⟨x,hb⟩).symm
  obtain ⟨U,hU,hUfalse,hUtrue⟩ :=
    Homeomorph.exists_union_finitePL (F false) (F true) (hF false) (hF true) hoverlap hagree
  have hUkeep (b : Bool) (x : B b) :
      (U ⟨x,by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : E × ℝ) = F b x := by
    cases b
    · exact hUfalse x
    · exact hUtrue x
  have hPunion : P false ∪ P true = (caps false false ∪ caps true false) ×ˢ I := by
    exact union_prod.symm
  let U' := U.trans (Homeomorph.setCongr hPunion)
  have hU' : U'.IsFinitePL := hU.setCongr rfl hPunion
  have hheight (s : Bool) (x : (B false ∪ B true : Set E)) :
      (x : E) ∈ caps false s ∪ caps true s ↔
        (U' x : E × ℝ).2 = if s then (1 : ℝ) else 0 := by
    constructor
    · intro hx
      have hside (b : Bool) (hb : (x : E) ∈ caps b s) :
          (U' x : E × ℝ).2 = if s then (1 : ℝ) else 0 := by
        have hv := hUkeep b ⟨x,hcapB b s hb⟩
        exact (congrArg Prod.snd hv).trans ((hcapsF b s ⟨x,hcapB b s hb⟩).mp hb).2
      rcases hx with hx | hx
      · exact hside false hx
      · exact hside true hx
    · intro hx
      have hside (b : Bool) (hb : (x : E) ∈ B b) : (x : E) ∈ caps b s := by
        apply (hcapsF b s ⟨x,hb⟩).mpr
        refine ⟨(F b ⟨x,hb⟩).property.1,?_⟩
        exact (congrArg Prod.snd (hUkeep b ⟨x,hb⟩)).symm.trans hx
      rcases x.property with hb | hb
      · exact Or.inl (hside false hb)
      · exact Or.inr (hside true hb)
  obtain ⟨S,hS,_,_⟩ := (hcaps false false).exists_sphere_model_of_disk_union
    (hcaps true false) hbase
  have hI := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hI
  have hid : (Homeomorph.refl (I : Set ℝ)).IsFinitePL :=
    ⟨id,⟨L,hL,hLs,L.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,fun _ => rfl⟩
  let V := (Homeomorph.Set.prod (caps false false ∪ caps true false) I).trans
    ((S.prodCongr (Homeomorph.refl I)).trans (Homeomorph.Set.prod (frontier (halfBall 1)) I).symm)
  refine ⟨U'.trans V,hU'.trans (hS.prod hid),?_⟩
  intro s x
  exact hheight s x

end Set
