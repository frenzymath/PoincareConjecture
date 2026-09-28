import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RimSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.AnnulusLevelCircles



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1



theorem exists_four_collar_rim_subcomplexes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (N : Bool → Set E) (C : Set E)
    (hdis : Disjoint (N false) (N true))
    (hspace : K.space = (N false ∪ N true) ∩ C)
    (c : ∀ b, squareAnnulus 1 (1 / 8) ≃ₜ N b) (hc : ∀ b, (c b).IsFinitePL)
    (hcut : ∀ b x, (c b x : E) ∈ C ↔
      depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8) :
    ∃ (B : Bool × Bool → SimplicialComplex ℝ E)
      (gamma : ∀ i, Q2 ≃ₜ (B i).space),
      (∀ i, B i ≤ K) ∧ (∀ i, (gamma i).IsFinitePL) ∧
      Pairwise (fun i j ↦ Disjoint (B i).space (B j).space) ∧
      (∀ s, s ∈ K.faces ↔ ∃ i, s ∈ (B i).faces) ∧
      (∀ i, (B i).space ⊆ N i.1) ∧
      ∀ i x, (c i.1 x : E) ∈ (B i).space ↔
        depth 1 x = if i.2 then (1 / 8 : ℝ) else -(1 / 8 : ℝ) := by
  classical
  have hu (b : Bool) : (if b then (1 / 8 : ℝ) else -(1 / 8 : ℝ)) ∈
      Icc (-(1 / 8 : ℝ)) (1 / 8) := by cases b <;> norm_num
  have H := fun i : Bool × Bool ↦ exists_finitePL_annulus_level_circle
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 1)
    (hu i.2) (c i.1) (hc i.1)
  choose S g hg hcompact hSN hlevel using H
  have hpair : Pairwise (fun i j ↦ Disjoint (S i) (S j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    by_cases hb : i.1 = j.1
    · let p := (c i.1).symm ⟨x, hSN i hxi⟩
      have hp : (c i.1 p : E) = x := congrArg Subtype.val ((c i.1).apply_symm_apply _)
      have hi := (hlevel i p).mp (hp ▸ hxi)
      have hj : depth 1 p = if j.2 then (1 / 8 : ℝ) else -(1 / 8 : ℝ) := by
        apply (hlevel j p).mp
        have he := congrArg (fun b ↦ (c b p : E)) hb
        rw [← he, hp]
        exact hxj
      have hs : i.2 ≠ j.2 := fun hs ↦ hij (Prod.ext hb hs)
      rcases i with ⟨b, s⟩
      rcases j with ⟨b', t⟩
      cases s <;> cases t <;> norm_num at hi hj hs <;> linarith
    · have hx0 : x ∈ N i.1 := hSN i hxi
      have hx1 : x ∈ N j.1 := hSN j hxj
      cases hi : i.1 <;> cases hj : j.1
      · exact hb (hi.trans hj.symm)
      · exact disjoint_left.mp hdis (hi ▸ hx0) (hj ▸ hx1)
      · exact disjoint_left.mp hdis (hj ▸ hx1) (hi ▸ hx0)
      · exact hb (hi.trans hj.symm)
  have hcover : (⋃ i, S i) = K.space := by
    rw [hspace]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hxN := hSN i hi
      let p := (c i.1).symm ⟨x, hxN⟩
      have hp : (c i.1 p : E) = x := congrArg Subtype.val ((c i.1).apply_symm_apply _)
      have hd := (hlevel i p).mp (hp ▸ hi)
      refine ⟨?_, ?_⟩
      · cases hi : i.1
        · exact Or.inl (hi ▸ hxN)
        · exact Or.inr (hi ▸ hxN)
      · rw [← hp, hcut]
        cases hs : i.2
        · exact Or.inl (by simpa only [hs, Bool.false_eq_true, ite_false] using hd)
        · exact Or.inr (by simpa only [hs, ite_true] using hd)
    · rintro ⟨hxN, hxC⟩
      have H (b : Bool) (hb : x ∈ N b) : x ∈ ⋃ i, S i := by
        let p := (c b).symm ⟨x, hb⟩
        have hp : (c b p : E) = x := congrArg Subtype.val ((c b).apply_symm_apply _)
        rcases (hcut b p).mp (hp ▸ hxC) with hd | hd
        · exact mem_iUnion.mpr ⟨(b, false), hp ▸ (hlevel (b, false) p).mpr hd⟩
        · exact mem_iUnion.mpr ⟨(b, true), hp ▸ (hlevel (b, true) p).mpr hd⟩
      exact hxN.elim (H false) (H true)
  obtain ⟨B, hBK, hBS, hfaces⟩ := exists_subcomplexes_of_disjoint_closed_cover K hK S
    (fun i ↦ (hcompact i).isClosed) hpair hcover
  let gamma := fun i ↦ (g i).trans (Homeomorph.setCongr (hBS i).symm)
  refine ⟨B, gamma, hBK, ?_, ?_, hfaces, ?_, ?_⟩
  · intro i
    obtain ⟨f, hf, hfv⟩ := hg i
    exact ⟨f, hf, hfv⟩
  · simpa only [hBS] using hpair
  · intro i
    simpa only [hBS] using hSN i
  · intro i x
    simpa only [hBS] using hlevel i x

end PoincareConjecture.M76.Dehn.Annuli
