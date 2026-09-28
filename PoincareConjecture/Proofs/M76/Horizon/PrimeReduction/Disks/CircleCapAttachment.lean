import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.PlanarCircleInnerDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.TaperingCapAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallReplacement









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem annulus_boundary_image_of_period
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (c : squareAnnulus 8 1 ≃ₜ B) (f : P2 → E)
    (hf : ∀ p : squareAnnulus 8 1, (c p : E) = f p)
    (φ : P2 → E)
    (hperiod : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * 8)) (u : Icc (-1 : ℝ) 1),
      (c ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) = φ (s,u))
    {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    f '' frontier (_root_.Dehn.annulusSquare 8 u) =
      (fun s => φ (s,u)) '' Icc 0 (4 * 8) := by
  have hsub : frontier (_root_.Dehn.annulusSquare 8 u) ⊆ squareAnnulus 8 1 := by
    intro p hp
    rw [mem_squareAnnulus_iff_depth,
      (_root_.Dehn.mem_frontier_annulusSquare_iff 8 u p).mp hp]
    exact hu
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨s,hs,hsp⟩ := exists_period_parameter_of_depth
      (by norm_num : (0:ℝ)<1) (by norm_num : (4:ℝ)*1<8) ⟨p,hsub hp⟩
    have hpdepth := (_root_.Dehn.mem_frontier_annulusSquare_iff 8 u p).mp hp
    rw [hpdepth] at hsp
    refine ⟨s,hs,?_⟩
    rw [← hf ⟨p,hsub hp⟩]
    exact (hperiod s hs ⟨u,hu⟩).symm.trans (congrArg (fun q => (c q : E))
      (Subtype.ext hsp.symm))
  · rintro ⟨s,hs,rfl⟩
    let p : squareAnnulus 8 1 :=
      ⟨annulusMap 8 (by norm_num) ((s:AddCircle (4*8:ℝ)),u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ ⟨u,hu⟩⟩
    refine ⟨p,?_,(hf p).symm.trans (hperiod s hs ⟨u,hu⟩)⟩
    apply (_root_.Dehn.mem_frontier_annulusSquare_iff 8 u p).mpr
    exact depth_annulusMap (by norm_num)
      (by have := abs_le.mpr hu; linarith) _

theorem attach_periodic_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B q o : Set E} (hA : IsFinitePLBallPair P2 A q)
    (hInter : A ∩ B = q) (c : squareAnnulus 8 1 ≃ₜ B) (hc : c.IsFinitePL)
    (φ : P2 → E)
    (hperiod : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * 8)) (u : Icc (-1 : ℝ) 1),
      (c ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) = φ (s,u))
    (hinner : (fun s => φ (s,1)) '' Icc 0 (4*8) = q)
    (houter : (fun s => φ (s,-1)) '' Icc 0 (4*8) = o) :
    IsFinitePLBallPair P2 (A ∪ B) o := by
  obtain ⟨f,hf,hcf⟩ := hc
  have hi := (annulus_boundary_image_of_period c f hcf φ hperiod (by norm_num : (1:ℝ)∈Icc (-1) 1)).trans hinner
  have ho := (annulus_boundary_image_of_period c f hcf φ hperiod (by norm_num : (-1:ℝ)∈Icc (-1) 1)).trans houter
  obtain ⟨hcover,hseam,hrim⟩ := _root_.Dehn.annulusSquare_partition (L:=8) (by norm_num : (0:ℝ)<1)
  have hsub : frontier (_root_.Dehn.annulusSquare 8 1) ⊆ squareAnnulus 8 1 := by
    rw [←hseam]
    exact inter_subset_right
  have hmem (p : squareAnnulus 8 1) :
      (p:P2) ∈ frontier (_root_.Dehn.annulusSquare 8 1) ↔ (c p:E)∈q := by
    rw [←hi]
    constructor
    · exact fun hp => ⟨p,hp,(hcf p).symm⟩
    · rintro ⟨x,hx,hxp⟩
      have heq : c ⟨x,hsub hx⟩ = c p := Subtype.ext ((hcf _).trans hxp)
      exact congrArg Subtype.val (c.injective heq) ▸ hx
  have hs : IsFinitePLBallPair P2
      (_root_.Dehn.annulusSquare 8 1 ∪ squareAnnulus 8 1)
      (frontier (_root_.Dehn.annulusSquare 8 (-1))) :=
    hcover.symm ▸ _root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num : 2*(-1:ℝ)<8)
  exact ho ▸ (hs.exists_piece_replacement
    (_root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num : 2*(1:ℝ)<8))
    hA hseam hInter hrim c ⟨f,hf,hcf⟩ hmem hcf).1



theorem attach_tapering_cap_annuli
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    (side : Bool) {A T : Set E}
    (hA : IsFinitePLBallPair P2 A
      ((fun t => τ ((0, if side then 1 / 2 else -1 / 2),t)) '' Icc 0 β))
    (hAT : A ⊆ T)
    (htriangle : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x ∈ T ↔ x.1 ∈ signedTubeSheet 0) :
    let B : Bool → Set E := fun positive =>
      (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
    (∀ positive : Bool,
      IsFinitePLBallPair P2 (A ∪ B positive)
        ((fun t => τ ((if positive then 1 / 4 else -1 / 4,0),t)) '' Icc 0 β) ∧
      (A ∪ B positive) ∩ T = A ∧
      A ∪ B positive ⊆ A ∪ τ '' (signedTubeDiamond ×ˢ Icc 0 β)) ∧
    (A ∪ B true) ∩ (A ∪ B false) = A := by
  classical
  dsimp only
  let B : Bool → Set E := fun positive =>
    (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
  let q : Set E := (fun t => τ ((0, if side then 1 / 2 else -1 / 2),t)) '' Icc 0 β
  have hq : (fun s => τ ((0, if side then 1 / 2 else -1 / 2), β/32*s)) ''
      Icc 0 (4*8) = q := cap_circle_period_rescaling hβ τ _
  obtain ⟨c,hc,hboth⟩ := exists_tapering_cap_annuli hβ τ hτ hfib side
  rw [hq] at hc hboth
  have hBT (positive : Bool) : B positive ∩ T = q := by
    rw [←(hc positive).2.2.2.2.1]
    ext y
    constructor
    · rintro ⟨hy,hT⟩
      obtain ⟨x,hx,rfl⟩ := (hc positive).2.2.2.1 hy
      exact ⟨hy, x, ⟨hx, (signedTubeSheet_coordinate_iff _ hx.1 0).mp
        ((htriangle x hx).mp hT)⟩, rfl⟩
    · rintro ⟨hy,x,⟨hx,hx0⟩,rfl⟩
      exact ⟨hy,(htriangle x hx).mpr
        ((signedTubeSheet_coordinate_iff _ hx.1 0).mpr hx0)⟩
  have hInter (positive : Bool) : A ∩ B positive = q := by
    apply Subset.antisymm
    · intro y hy
      exact (hBT positive).subset ⟨hy.2,hAT hy.1⟩
    · intro y hy
      exact ⟨hA.1 hy, ((hBT positive).symm.subset hy).1⟩
  refine ⟨?_,?_⟩
  · intro positive
    refine ⟨?_,?_,union_subset_union_right A (hc positive).2.2.2.1⟩
    · apply attach_periodic_annulus hA (hInter positive) (c positive)
        (hc positive).1 (τ ∘ taperingCapStrip β side positive) (hc positive).2.2.1
      · have hv (s : ℝ) : taperingCapStrip β side positive (s,1) =
            ((0,if side then 1/2 else -1/2),β/32*s) := by
          cases side <;> cases positive <;> norm_num [taperingCapStrip_apply]
        simpa only [Function.comp_apply, hv] using hq
      · have hv (s : ℝ) : taperingCapStrip β side positive (s,-1) =
            ((if positive then 1/4 else -1/4,0),β/32*s) := by
          cases side <;> cases positive <;> norm_num [taperingCapStrip_apply]
        simpa only [Function.comp_apply, hv] using cap_circle_period_rescaling hβ τ
          (if positive then 1/4 else -1/4,0)
    · ext y
      constructor
      · rintro ⟨hy,hT⟩
        rcases hy with hy | hy
        · exact hy
        · exact hA.1 ((hBT positive).subset ⟨hy,hT⟩)
      · exact fun hy => ⟨Or.inl hy,hAT hy⟩
  · ext y
    constructor
    · rintro ⟨hy,hz⟩
      rcases hy with hy | hy
      · exact hy
      rcases hz with hz | hz
      · exact hz
      exact hA.1 (hboth.subset ⟨hy,hz⟩)
    · exact fun hy => ⟨Or.inl hy,Or.inl hy⟩



theorem attached_cap_sphere_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    (side : Bool) {A S : Set E} (hAS : Disjoint A S)
    (hsphere : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x ∈ S ↔ x.1 ∈ signedTubeSheet 1) (positive : Bool) :
    (A ∪ (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4*8) ×ˢ Icc (-1) 1)) ∩ S =
      (fun t => τ ((if positive then 1/4 else -1/4,0),t)) '' Icc 0 β := by
  obtain ⟨c,hc,_⟩ := exists_tapering_cap_annuli hβ τ hτ hfib side
  rw [←cap_circle_period_rescaling hβ τ (if positive then 1/4 else -1/4,0),
    ←(hc positive).2.2.2.2.2]
  ext y
  constructor
  · rintro ⟨hy,hyS⟩
    rcases hy with hy | hy
    · exact (Set.disjoint_left.mp hAS hy hyS).elim
    · obtain ⟨x,hx,rfl⟩ := (hc positive).2.2.2.1 hy
      exact ⟨hy,x,⟨hx,(signedTubeSheet_coordinate_iff _ hx.1 1).mp
        ((hsphere x hx).mp hyS)⟩,rfl⟩
  · rintro ⟨hy,x,⟨hx,hx0⟩,rfl⟩
    exact ⟨Or.inr hy,(hsphere x hx).mpr
      ((signedTubeSheet_coordinate_iff _ hx.1 1).mpr hx0)⟩



theorem exists_attached_circle_cap_disks
    {n : ℕ} (L : Polygon V3 (n + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) {D T : Set V3}
    (hD : IsFinitePLBallPair P2 D (L.boundary ℝ)) (hDT : D ⊆ T)
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F) (hFR : EqOn (F ∘ R) id T)
    {β : ℝ} (hβ : 0 < β) (τ : C3 → V3)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (htriangle : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x ∈ T ↔ x.1 ∈ signedTubeSheet 0)
    (haxis : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x ∈ L.boundary ℝ ↔ x.1 = (0,0))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β))) :
    ∃ (side : Bool) (m : ℕ) (P : Polygon V3 (m + 3)) (inner : Set V3),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      P.boundary ℝ =
        (fun t => τ ((0, if side then 1/2 else -1/2),t)) '' Icc 0 β ∧
      IsFinitePLBallPair P2 inner (P.boundary ℝ) ∧
      inner ⊆ D \ L.boundary ℝ ∧
      (∀ c ∈ Ioc (0:ℝ) 1, ∀ t ∈ Icc 0 β,
        τ ((0,if side then c else -c),t) ∈ D \ L.boundary ℝ) ∧
      (∀ c ∈ Ioc (0:ℝ) 1, ∀ t ∈ Icc 0 β,
        τ ((0,if side then -c else c),t) ∉ D) ∧
      let B : Bool → Set V3 := fun positive =>
        (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4*8) ×ˢ Icc (-1) 1)
      (∀ positive : Bool,
        IsFinitePLBallPair P2 (inner ∪ B positive)
          ((fun t => τ ((if positive then 1/4 else -1/4,0),t)) '' Icc 0 β) ∧
        (inner ∪ B positive) ∩ T = inner ∧
        inner ∪ B positive ⊆ inner ∪ τ '' (signedTubeDiamond ×ˢ Icc 0 β)) ∧
      (inner ∪ B true) ∩ (inner ∪ B false) = inner := by
  obtain ⟨side,hinside,houtside,m,P,inner,hPi,hP,hPr,hinner,hsub⟩ :=
    exists_inner_disk_of_identity_circle_tube L hL hLi hD hDT F R hRF hFR
      hβ τ hτ htriangle haxis hfib
  refine ⟨side,m,P,inner,hPi,hP,hPr,hinner,hsub,hinside,houtside,?_⟩
  exact attach_tapering_cap_annuli hβ τ hτ
    (by intro x hx y hy; simpa only [and_comm] using hfib x hx y hy)
    side (hPr ▸ hinner) (fun _ hx => hDT (hsub hx).1) htriangle

end PoincareConjecture.M76
