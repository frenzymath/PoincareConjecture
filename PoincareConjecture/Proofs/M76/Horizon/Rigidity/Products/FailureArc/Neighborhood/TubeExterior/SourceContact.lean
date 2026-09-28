import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CutGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.CanonicalComplement



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem originalStripSheet_mem_lateral (j : Bool) {p : P2} (hp : p ∈ source) :
    originalStripSheet j p ∈ lateral 1 ↔ p ∈ arm (-1) ∪ arm 1 := by
  have hfront : frontier (transverseSquare 1) =
      (Icc (-1 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) ∪
      (({-1,1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1) := by
    rw [transverseSquare,frontier_prod_eq,isClosed_Icc.closure_eq,
      frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
  have hn : -p.2 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1,hp.2.2]
  cases j <;>
    simp [lateral,hfront,originalStripSheet,arm,hp.1,hp.2,hn,
      neg_eq_iff_eq_neg,or_comm]

theorem strip_complement_contacts
    {X : Type*} {S E : Set P2} {f : P2 → X} {c : P2 → P2} {τ : C3 → X}
    (j : Bool) (hτ : InjOn τ tube)
    (hpre : S ∩ f ⁻¹' (τ '' tube) = c '' source)
    (hsheet : ∀ p ∈ source, f (c p) = τ (originalStripSheet j p))
    (hES : E ⊆ S)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    ∀ x ∈ E, f x ∉ τ '' openTube 1 ∧
      (f x ∈ τ '' lateral 1 ↔ x ∈ c '' (arm (-1) ∪ arm 1)) := by
  have harm : arm (-1) ∪ arm 1 ⊆ source := by
    rintro p (hp | hp)
    all_goals exact ⟨hp.1,by rw [show p.2 = _ from hp.2]; norm_num⟩
  have htube : closedTube 1 = tube := rfl
  have hfar (x : P2) (hx : x ∈ E) (hp : f x ∈ τ '' tube) :
      x ∈ c '' (arm (-1) ∪ arm 1) :=
    hcontact.subset ⟨hx,hpre.subset ⟨hES hx,hp⟩⟩
  intro x hx
  constructor
  · rintro ⟨z,hz,hzx⟩
    obtain ⟨p,hp,hpx⟩ := hfar x hx
      ⟨z,htube.subset (openTube_subset 1 hz),hzx⟩
    have hpS := harm hp
    have heq : originalStripSheet j p = z := hτ (originalStripSheet_mem_tube j hpS)
      (htube.subset (openTube_subset 1 hz)) ((hsheet p hpS).symm.trans (hpx ▸ hzx.symm))
    have hlat := (originalStripSheet_mem_lateral j hpS).mpr hp
    rw [heq,← closedTube_sdiff_openTube 1] at hlat
    exact hlat.2 hz
  · constructor
    · rintro ⟨z,hz,hzx⟩
      exact hfar x hx ⟨z,htube.subset (lateral_subset 1 hz),hzx⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨originalStripSheet j p,(originalStripSheet_mem_lateral j (harm hp)).mpr hp,
        (hsheet p (harm hp)).symm⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem strip_complement_exhausts_exterior
    {S E : Set P2} {f : P2 → X} {c : P2 → P2} {τ : C3 → X}
    (j : Bool) (hfR : MapsTo f S R) (hτ : InjOn τ tube)
    (hpre : S ∩ f ⁻¹' (τ '' tube) = c '' source)
    (hsheet : ∀ p ∈ source, f (c p) = τ (originalStripSheet j p))
    (hES : E ⊆ S) (hcover : E ∪ c '' source = S)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    (f '' S) ∩ (R \ τ '' openTube 1) = f '' E := by
  have h := strip_complement_contacts j hτ hpre hsheet hES hcontact
  ext x
  constructor
  · rintro ⟨⟨p,hp,rfl⟩,_,hn⟩
    have hpE : p ∈ E := by
      rcases hcover.symm.subset hp with hE | ⟨q,hq,rfl⟩
      · exact hE
      · have hl : originalStripSheet j q ∈ lateral 1 := by
          rw [← closedTube_sdiff_openTube 1]
          refine ⟨originalStripSheet_mem_tube j hq,?_⟩
          intro hqU
          exact hn ⟨originalStripSheet j q,hqU,(hsheet q hq).symm⟩
        exact (hcontact.symm.subset
          ⟨q,(originalStripSheet_mem_lateral j hq).mp hl,rfl⟩).1
    exact ⟨p,hpE,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hES hp,rfl⟩,hfR (hES hp),(h p hp).1⟩

theorem OriginalIntervalTube.first_complement_proper
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hfR : MapsTo f₀ S R)
    (hfproper : ∀ x ∈ S, f₀ x ∈ frontier R ↔ x ∈ frontier S)
    {E : Set P2} (hES : E ⊆ S)
    (hcontact : E ∩ (U.first '' source) = U.first '' (arm (-1) ∪ arm 1))
    (hboundary : frontier E = (E ∩ frontier S) ∪ U.first '' (arm (-1) ∪ arm 1)) :
    MapsTo f₀ E (R \ U.map '' openTube 1) ∧
      ∀ x ∈ E, f₀ x ∈ frontier (R \ U.map '' openTube 1) ↔ x ∈ frontier E := by
  have hi : InjOn U.map tube := fun x hx y hy h =>
    congrArg Subtype.val (U.embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  have h := strip_complement_contacts false hi U.first_preimage U.first_sheet hES hcontact
  refine ⟨fun x hx => ⟨hfR (hES hx),(h x hx).1⟩,?_⟩
  intro x hx
  rw [OriginalIntervalTube.frontier_exterior U hR he (by norm_num : (0 : ℝ) < 1) le_rfl,
    hboundary]
  simp only [mem_union,mem_sdiff,mem_inter_iff,hx,true_and,
    (h x hx).2,(h x hx).1,not_false_eq_true,and_true,hfproper x (hES hx)]

theorem OriginalIntervalTube.second_complement_proper
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hfR : MapsTo f₁ T R)
    (hfproper : ∀ x ∈ T, f₁ x ∈ frontier R ↔ x ∈ frontier T)
    {E : Set P2} (hES : E ⊆ T)
    (hcontact : E ∩ (U.second '' source) = U.second '' (arm (-1) ∪ arm 1))
    (hboundary : frontier E = (E ∩ frontier T) ∪ U.second '' (arm (-1) ∪ arm 1)) :
    MapsTo f₁ E (R \ U.map '' openTube 1) ∧
      ∀ x ∈ E, f₁ x ∈ frontier (R \ U.map '' openTube 1) ↔ x ∈ frontier E := by
  have hi : InjOn U.map tube := fun x hx y hy h =>
    congrArg Subtype.val (U.embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  have h := strip_complement_contacts true hi U.second_preimage U.second_sheet hES hcontact
  refine ⟨fun x hx => ⟨hfR (hES hx),(h x hx).1⟩,?_⟩
  intro x hx
  rw [OriginalIntervalTube.frontier_exterior U hR he (by norm_num : (0 : ℝ) < 1) le_rfl,
    hboundary]
  simp only [mem_union,mem_sdiff,mem_inter_iff,hx,true_and,
    (h x hx).2,(h x hx).1,not_false_eq_true,and_true,hfproper x (hES hx)]

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
