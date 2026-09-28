import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Pasting
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

def block (i : Fin 8) : Set P2 := Icc (i.val : ℝ) (i.val + 1) ×ˢ I

noncomputable def shift (i : Fin 8) : P2 →ᴬ[ℝ] P2 :=
  (ContinuousAffineEquiv.constVAdd ℝ P2 (-(i.val : ℝ), 0)).toContinuousAffineMap

theorem shift_value (i : Fin 8) (p : P2) : shift i p = (p.1 - i.val, p.2) := by
  change (-(i.val : ℝ) + p.1, 0 + p.2) = (p.1 - i.val,p.2)
  simp only [sub_eq_add_neg,add_comm,add_zero]

theorem shift_mapsTo (i : Fin 8) : MapsTo (shift i) (block i) Rect := by
  intro p hp
  rw [shift_value]
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩

theorem block_cover : (⋃ i : Fin 8, block i) = Icc (0 : ℝ) 8 ×ˢ I := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    exact ⟨⟨(Nat.cast_nonneg i.val).trans hi.1.1, by linarith [hi.1.2]⟩, hi.2⟩
  · intro hp
    have hp' : p.1 ∈ ⋃ i : Fin 8, segment ℝ (i.val : ℝ) (i.val + 1) := by
      simpa only [iUnion_nat_unit_segments, Nat.cast_ofNat,show (7 : ℝ) + 1 = 8 by norm_num] using hp.1
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp'
    rw [segment_eq_Icc (by linarith : (i.val : ℝ) ≤ i.val + 1)] at hi
    exact mem_iUnion.mpr ⟨i, hi, hp.2⟩

theorem exists_original_cut_strip
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V}
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (f : Fin 8 → P2 → X) (hf : ∀ i, PolyhedralPLInCharts e (f i) Rect)
    (hseam : ∀ i j : Fin 8, i.val + 1 = j.val →
      ∀ t ∈ I, f i (1,t) = f j (0,t)) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g (Icc (0 : ℝ) 8 ×ˢ I) ∧
      (∀ i p, p ∈ block i → g p = f i (p.1 - i.val,p.2)) ∧
      g '' (Icc (0 : ℝ) 8 ×ˢ I) = ⋃ i, f i '' Rect ∧
      (∀ i x, x ∈ Rect → g (x.1 + i.val,x.2) = f i x) := by
  classical
  have htri (i : Fin 8) : ∃ K : SimplicialComplex ℝ P2,
      K.faces.Finite ∧ K.space = block i := by
    have hball := (isFinitePLBallPair_Icc (show (i.val : ℝ) < i.val + 1 by linarith)).prod
      (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
    exact ⟨K,hK,hKs⟩
  choose K hK hKs using htri
  have hPL (i : Fin 8) : PolyhedralPLInCharts e (f i ∘ shift i) (K i).space :=
    (hf i).comp_finitePiecewiseAffineOn (K i) (hK i)
      ⟨K i,hK i,rfl,(K i).affineOnFaces_affine (shift i)⟩
      (fun _ hp => shift_mapsTo i (hKs i ▸ hp))
  have hagree (i j : Fin 8) (p : P2) (hi : p ∈ block i) (hj : p ∈ block j) :
      f i (shift i p) = f j (shift j p) := by
    suffices hordered : ∀ i j : Fin 8, i < j → p ∈ block i → p ∈ block j →
        f i (shift i p) = f j (shift j p) by
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact hordered i j hij hi hj
      · rfl
      · exact (hordered j i hji hj hi).symm
    intro i j hij hi hj
    have hn : i.val + 1 = j.val := by
      have hcast : (j.val : ℝ) ≤ i.val + 1 := hj.1.1.trans hi.1.2
      have hnat : j.val ≤ i.val + 1 := by exact_mod_cast hcast
      have hlt : i.val < j.val := hij
      omega
    have hcast : (j.val : ℝ) = i.val + 1 := by exact_mod_cast hn.symm
    have hp : p.1 = j.val := by linarith [hi.1.2, hj.1.1]
    rw [shift_value,shift_value]
    have hleft : p.1 - i.val = 1 := by linarith
    have hright : p.1 - j.val = 0 := by linarith
    rw [hleft,hright]
    exact hseam i j hn p.2 hi.2
  obtain ⟨g,hg,hvalue,_,_⟩ := exists_original_panel_pasting hcover hcompat K hK
    (fun i => f i ∘ shift i) (f 0 (0,0)) hPL
    (fun i j p hi hj => hagree i j p (hKs i ▸ hi) (hKs j ▸ hj))
  have hsource : (⋃ i, (K i).space) = Icc (0 : ℝ) 8 ×ˢ I := by
    simp only [hKs]
    exact block_cover
  have hval (i : Fin 8) (p : P2) (hp : p ∈ block i) :
      g p = f i (p.1 - i.val,p.2) := by
    simpa only [Function.comp_apply,shift_value] using hvalue i (hKs i |>.symm ▸ hp)
  have hcopy (i : Fin 8) (x : P2) (hx : x ∈ Rect) :
      g (x.1 + i.val,x.2) = f i x := by
    have hm : (x.1 + i.val,x.2) ∈ block i :=
      ⟨⟨by linarith [hx.1.1],by linarith [hx.1.2]⟩,hx.2⟩
    simpa only [add_sub_cancel_right,Prod.mk.eta] using hval i _ hm
  refine ⟨g,hsource ▸ hg,hval,?_,hcopy⟩
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (block_cover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨i,shift i p,shift_mapsTo i hi,
      (congrArg (f i) (shift_value i p)).trans (hval i p hi).symm⟩
  · intro hy
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hy
    have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    exact ⟨(x.1 + i.val,x.2),
      ⟨⟨by linarith [hx.1.1,Nat.cast_nonneg (α := ℝ) i.val],by linarith [hx.1.2]⟩,hx.2⟩,
      hcopy i x hx⟩

theorem cut_strip_level_image {X : Type*} (f : Fin 8 → P2 → X) (g : P2 → X)
    (hvalue : ∀ i p, p ∈ block i → g p = f i (p.1 - i.val,p.2))
    {t : ℝ} (ht : t ∈ I) :
    g '' (Icc (0 : ℝ) 8 ×ˢ {t}) = ⋃ i, f i '' (I ×ˢ {t}) := by
  ext y
  constructor
  · rintro ⟨⟨s,u⟩,⟨hs,hu⟩,rfl⟩
    change u = t at hu
    subst u
    obtain ⟨i,hi⟩ := mem_iUnion.mp (block_cover.symm.subset
      (show (s,t) ∈ Icc (0 : ℝ) 8 ×ˢ I from ⟨hs,ht⟩))
    exact mem_iUnion.mpr ⟨i,(s - i.val,t),
      ⟨⟨by linarith [hi.1.1],by linarith [hi.1.2]⟩,rfl⟩,(hvalue i (s,t) hi).symm⟩
  · intro hy
    obtain ⟨i,⟨s,u⟩,⟨hs,hu⟩,rfl⟩ := mem_iUnion.mp hy
    change u = t at hu
    subst u
    have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    refine ⟨(s + i.val,t),⟨⟨by linarith [hs.1,Nat.cast_nonneg (α := ℝ) i.val],
      by linarith [hs.2]⟩,rfl⟩,?_⟩
    simpa only [add_sub_cancel_right] using hvalue i (s + i.val,t)
      (show (s + i.val,t) ∈ block i from ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,ht⟩)

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
