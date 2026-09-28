import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Annulus
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus (2 : ℝ) (1 / 8)

noncomputable def stripCoordinates : P2 →ᴬ[ℝ] P2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    ((4 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ P2 (1 / 2))

theorem stripCoordinates_value (p : P2) : stripCoordinates p = (p.1,4 * p.2 + 1 / 2) := rfl

theorem exists_original_eight_panel_annulus
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V}
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (f : Fin 8 → P2 → X) (hf : ∀ i, PolyhedralPLInCharts e (f i) Rect)
    (hfi : ∀ i, InjOn (f i) Rect)
    (hseam : ∀ i j : Fin 8, i.val + 1 = j.val → ∀ t ∈ I, f i (1,t) = f j (0,t))
    (hclose : ∀ t ∈ I, f 7 (1,t) = f 0 (0,t))
    (hcontact : ∀ i j : Fin 8, i.val + 1 = j.val →
      (f i '' Rect) ∩ (f j '' Rect) = f i '' ({1} ×ˢ I))
    (hend : (f 0 '' Rect) ∩ (f 7 '' Rect) = f 0 '' ({0} ×ˢ I))
    (hfar : ∀ i j : Fin 8, i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = 7) → Disjoint (f i '' Rect) (f j '' Rect)) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g Ann ∧
      Topology.IsEmbedding (fun x : Ann => g x) ∧
      g '' Ann = ⋃ i, f i '' Rect ∧
      (∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val + 1) →
        ∀ u : Icc (-(1 / 8 : ℝ)) (1 / 8),
        g (annulusMap 2 (by norm_num) ((s : AddCircle (4 * (2 : ℝ))),u)) =
          f i (s - i.val,4 * (u : ℝ) + 1 / 2)) ∧
      g '' frontier (_root_.Dehn.annulusSquare 2 (-(1 / 8))) =
        ⋃ i, f i '' (I ×ˢ {0}) ∧
      g '' frontier (_root_.Dehn.annulusSquare 2 (1 / 8)) =
        ⋃ i, f i '' (I ×ˢ {1}) := by
  obtain ⟨σ,hσ,hvalue,himage,_⟩ := exists_original_cut_strip hcover hcompat f hf hseam
  have hfib := cut_strip_fibers f σ hfi hseam hclose hcontact hend hfar hvalue
  have hcoord : MapsTo stripCoordinates (rectangle (4 * (2 : ℝ)) (1 / 8))
      (Icc (0 : ℝ) 8 ×ˢ I) := by
    intro p hp
    change p.1 ∈ Icc 0 8 ∧ 4 * p.2 + 1 / 2 ∈ I
    exact ⟨by convert hp.1 using 1; norm_num,⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩⟩
  have hcoordsimage : stripCoordinates '' rectangle (4 * (2 : ℝ)) (1 / 8) =
      Icc (0 : ℝ) 8 ×ˢ I := by
    apply Subset.antisymm (image_subset_iff.mpr hcoord)
    intro p hp
    exact ⟨(p.1,(p.2 - 1 / 2) / 4),
      ⟨by convert hp.1 using 1; norm_num,by constructor <;> linarith [hp.2.1,hp.2.2]⟩,
      Prod.ext rfl (by dsimp [stripCoordinates]; ring)⟩
  have hball := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 2)).prod
    (isFinitePLBallPair_Icc (by norm_num : -(1 / 8 : ℝ) < 1 / 8))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  change K.space = rectangle (4 * (2 : ℝ)) (1 / 8) at hKs
  have hφ : PolyhedralPLInCharts e (σ ∘ stripCoordinates)
      (rectangle (4 * (2 : ℝ)) (1 / 8)) := by
    have h := hσ.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,K.affineOnFaces_affine stripCoordinates⟩
      (fun _ hx => hcoord (hKs ▸ hx))
    exact hKs ▸ h
  let : Fact (0 < 4 * (2 : ℝ)) := ⟨by norm_num⟩
  have hφfib : ∀ x ∈ rectangle (4 * (2 : ℝ)) (1 / 8),
      ∀ y ∈ rectangle (4 * (2 : ℝ)) (1 / 8),
      (σ ∘ stripCoordinates) x = (σ ∘ stripCoordinates) y ↔
        x.2 = y.2 ∧ (x.1 : AddCircle (4 * (2 : ℝ))) = (y.1 : AddCircle (4 * (2 : ℝ))) := by
    intro x hx y hy
    rw [AddCircle.coe_eq_coe_iff_eq_or_endpoints hx.1 hy.1]
    change σ (stripCoordinates x) = σ (stripCoordinates y) ↔ _
    rw [hfib _ (hcoord hx) _ (hcoord hy)]
    simp only [stripCoordinates_value,Prod.mk.injEq,show 4 * (2 : ℝ) = 8 by norm_num]
    constructor
    · rintro (⟨hs,ht⟩ | ⟨hs,hs',ht⟩ | ⟨hs,hs',ht⟩)
      · exact ⟨by linarith,Or.inl hs⟩
      · exact ⟨by linarith,Or.inr (Or.inl ⟨hs,hs'⟩)⟩
      · exact ⟨by linarith,Or.inr (Or.inr ⟨hs',hs⟩)⟩
    · rintro ⟨ht,hs | ⟨hs,hs'⟩ | ⟨hs,hs'⟩⟩
      · exact Or.inl ⟨hs,by rw [ht]⟩
      · exact Or.inr (Or.inl ⟨hs,hs',by rw [ht]⟩)
      · exact Or.inr (Or.inr ⟨hs',hs,by rw [ht]⟩)
  obtain ⟨g,hg,hgi,hgimage,hperiod,hlevels⟩ := exists_original_annulus_of_periodic_strip
    hcompat (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 2)
    (σ ∘ stripCoordinates) hφ hφfib
  have hlevelimage (v : ℝ) : stripCoordinates '' (Icc (0 : ℝ) (4 * 2) ×ˢ {v}) =
      Icc (0 : ℝ) 8 ×ˢ {4 * v + 1 / 2} := by
    ext z
    constructor
    · rintro ⟨⟨s,u⟩,⟨hs,hu⟩,rfl⟩
      change u = v at hu
      subst u
      change s ∈ Icc 0 8 ∧ 4 * v + 1 / 2 ∈ ({4 * v + 1 / 2} : Set ℝ)
      exact ⟨by convert hs using 1; norm_num,rfl⟩
    · rintro ⟨hs,hu⟩
      exact ⟨(z.1,v),⟨by convert hs using 1; norm_num,rfl⟩,Prod.ext rfl hu.symm⟩
  have hrim (v : ℝ) (hv : v ∈ Icc (-(1 / 8 : ℝ)) (1 / 8)) :
      frontier (_root_.Dehn.annulusSquare 2 v) = {x ∈ Ann | depth 2 x = v} := by
    ext x
    rw [_root_.Dehn.mem_frontier_annulusSquare_iff,mem_ofPred_eq]
    exact ⟨fun hx => ⟨mem_squareAnnulus_iff_depth.mpr (hx.symm ▸ hv),hx⟩,And.right⟩
  refine ⟨g,hg,hgi,?_,?_,?_,?_⟩
  · rw [hgimage,image_comp,hcoordsimage,himage]
  · intro i s hs u
    have hs8 : s ∈ Icc 0 (4 * (2 : ℝ)) := by
      have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      exact ⟨(Nat.cast_nonneg i.val).trans hs.1,by linarith [hs.2]⟩
    rw [hperiod s hs8 u]
    exact hvalue i _ ⟨hs,(hcoord (show (s,(u : ℝ)) ∈ rectangle (4 * (2 : ℝ)) (1 / 8)
      from ⟨hs8,u.property⟩)).2⟩
  · rw [hrim _ (by norm_num),hlevels _ (by norm_num),image_comp,hlevelimage]
    norm_num
    exact cut_strip_level_image f σ hvalue (by norm_num : (0 : ℝ) ∈ I)
  · rw [hrim _ (by norm_num),hlevels _ (by norm_num),image_comp,hlevelimage]
    norm_num
    exact cut_strip_level_image f σ hvalue (by norm_num : (1 : ℝ) ∈ I)

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
