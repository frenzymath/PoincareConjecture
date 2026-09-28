import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Local
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.RelativeDiskPushHomotopy



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

open PolygonalCrossingResolution BoundaryCup
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_local_returning_arc_removal_with_cup_homotopy
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R O : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hO : IsOpen O)
    {c₀ c₁ : P2 → P2}
    (hc₀ : FinitePiecewiseAffineOn c₀ source) (hi₀ : InjOn c₀ source)
    (hc₁ : FinitePiecewiseAffineOn c₁ source) (hi₁ : InjOn c₁ source)
    {D U Q N U' B V D₁ E₁ S₀ S₁ : Set P2}
    (hD : IsFinitePLBallPair P2 D (U ∪ c₀ '' arm 0))
    (hB : IsFinitePLBallPair P2 B (V ∪ c₁ '' arm 1))
    (hU : IsFinitePLBallPair ℝ U {c₀ (0, 0), c₀ (1, 0)})
    (hV : IsFinitePLBallPair ℝ V {c₁ (0, 1), c₁ (1, 1)})
    (hUW : U ∩ (c₀ '' arm 0) = {c₀ (0, 0), c₀ (1, 0)})
    (hVZ : V ∩ (c₁ '' arm 1) = {c₁ (0, 1), c₁ (1, 1)})
    (hcontact : D ∩ (c₀ '' halfSource false) = c₀ '' arm 0)
    (houter : D ∩ Q = U) (hNouter : N ∩ Q = U')
    (hcQ : ∀ p ∈ source, c₀ p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1)
    (hN : N = D ∪ c₀ '' halfSource false)
    (hNball : IsFinitePLBallPair P2 N (U' ∪ c₀ '' arm (-1)))
    (hU' : IsFinitePLBallPair ℝ U' {c₀ (0, -1), c₀ (1, -1)})
    (hnewContact : U' ∩ (c₀ '' arm (-1)) = {c₀ (0, -1), c₀ (1, -1)})
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁) (hE₁ : IsCompact E₁)
    (hNS₀ : N ⊆ S₀) (hBS₁ : B ⊆ S₁) (hc₁S : MapsTo c₁ source S₁)
    (hsource : S₁ ⊆ E₁ ∪ D₁) (hED : E₁ ∩ D₁ = c₁ '' arm 0)
    (htrim : B ∩ (c₁ '' halfSource true) = c₁ '' arm 1)
    (htrimCover : (c₁ '' halfSource true) ∪ B = D₁)
    {f₀ f₁ : P2 → X}
    (hf₀ : PolyhedralPLInCharts e f₀ S₀) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hi₀f : InjOn f₀ S₀) (hi₁f : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ S₀ R) (hf₁R : MapsTo f₁ S₁ R)
    (hf₀O : MapsTo f₀ N O) (hf₁O : MapsTo f₁ B O)
    (hf₀proper : ∀ x ∈ N, f₀ x ∈ frontier R ↔ x ∈ U')
    (hf₁proper : ∀ x ∈ B, f₁ x ∈ frontier R ↔ x ∈ V)
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (hτR : MapsTo τ tube R) (hτO : MapsTo τ tube O)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hA : ∀ z ∈ tube, τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hT : ∀ z ∈ tube, τ z ∈ f₀ '' S₀ ↔ z.1.2 = -z.1.1)
    (hBT : Disjoint (f₁ '' B) (f₀ '' S₀))
    (hfar₀ : ∀ t : I, f₀ (c₀ ((t : ℝ), -1)) = τ ((-1, 1), (t : ℝ)))
    (hperiod₁ : ∀ p ∈ source, f₁ (c₁ p) = τ ((p.2, p.2), p.1)) :
    ∃ v k : P2 → X,
      PolyhedralPLInCharts e v N ∧ InjOn v N ∧
      EqOn v f₀ (c₀ '' arm (-1)) ∧
      (v '' N) ∩ (f₁ '' S₁) = f₁ '' B ∧
      (v '' N) ∩ (f₀ '' S₀) = f₀ '' (c₀ '' arm (-1)) ∧
      v '' N = f₁ '' B ∪ τ '' (BoundaryCup.bridgeCoordinates '' halfSource false) ∧
      MapsTo v N R ∧ (∀ x ∈ N,v x ∈ frontier R ↔ x ∈ U') ∧
      PolyhedralPLInCharts e k N ∧ InjOn k N ∧
      MapsTo k N R ∧ MapsTo k N O ∧ EqOn k f₀ (c₀ '' arm (-1)) ∧
      Disjoint (k '' N) (f₁ '' S₁) ∧
      (∀ x ∈ N, k x ∈ f₀ '' S₀ ↔ x ∈ c₀ '' arm (-1)) ∧
      (∀ x ∈ N, k x ∈ frontier R ↔ x ∈ U') ∧
      ∃ H : C(I × ↥N,X),
        (∀ x : N,H (⟨0,by norm_num⟩,x) = v x) ∧
        (∀ x : N,H (⟨1,by norm_num⟩,x) = k x) ∧
        (∀ z,H z ∈ R) ∧
        (∀ z,H z ∈ frontier R ↔ v z.2 ∈ frontier R) ∧
        ∀ z,(z.2:P2) ∈ c₀ '' arm (-1) → H z = v z.2 := by
  have hfar₁ (t : I) : f₁ (c₁ ((t : ℝ), 1)) = τ ((1, 1), (t : ℝ)) :=
    hperiod₁ _ ⟨t.property, by norm_num⟩
  have hf₁B : PolyhedralPLInCharts e f₁ B := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hB
    rw [← hKs]
    exact hf₁.restrict_finite K hK (hKs.subset.trans hBS₁)
  have hf₀N : PolyhedralPLInCharts e f₀ N := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hNball
    rw [← hKs]
    exact hf₀.restrict_finite K hK (hKs.subset.trans hNS₀)
  obtain ⟨v, hv, hvi, hkeep, hcapA, hcapT, himage, hvR, hvproper⟩ :=
    exists_original_boundary_cup_map he.compatible hc₀ hi₀ hc₁ hi₁ hD hB hU hV hUW hVZ
      hcontact houter hcQ f₀ f₁ hf₁B (hi₁f.mono hBS₁) hτ hτi (image_mono hBS₁)
      hBT hA hT (fun x hx ↦ hf₁R (hBS₁ hx)) hτR hf₁proper hτfront hfar₀ hfar₁
  rw [← hN] at hv hvi hcapA hcapT himage hvR hvproper
  have hW : IsFinitePLBallPair ℝ (c₀ '' arm (-1)) {c₀ (0, -1), c₀ (1, -1)} := by
    have hh := (exists_arm_parameter (-1)).1.image_of_subset hc₀
      (arm_far_subset_source false) hi₀
    simpa only [image_pair] using hh
  have hends : c₀ (0, -1) ≠ c₀ (1, -1) := by
    intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst
      (hi₀ (by norm_num [source]) (by norm_num [source]) h)
    norm_num at h01
  have hWN : c₀ '' arm (-1) ⊆ N := subset_union_right.trans hNball.1
  have hvproper' (x : P2) (hx : x ∈ N) : v x ∈ frontier R ↔ x ∈ U' :=
    (hvproper x hx).trans ⟨fun h ↦ hNouter.subset ⟨hx, h⟩, fun h ↦ (hNouter.superset h).2⟩
  have hcontact' : (v '' N) ∩ (f₀ '' N) = f₀ '' (c₀ '' arm (-1)) := by
    apply Subset.antisymm
    · intro z hz
      exact hcapT.subset ⟨hz.1, image_mono hNS₀ hz.2⟩
    · rintro z ⟨x, hx, rfl⟩
      exact ⟨⟨x, hWN hx, hkeep hx⟩, ⟨x, hWN hx, rfl⟩⟩
  obtain ⟨g, hg, hgi, hgR, hgproper, hgimage⟩ := exists_original_proper_disk_from_cup
    he.compatible hNball hU' hW hnewContact hends hv hf₀N hvi (hi₀f.mono hNS₀)
      hkeep hcontact' hvR (fun x hx ↦ hf₀R (hNS₀ hx)) hvproper' hf₀proper
  let Sigma := g '' BoundaryUnionDisk.whole
  have hCS : f₁ '' B ⊆ Sigma := fun _ hx ↦ hgimage.superset (Or.inl (hcapA.superset hx).1)
  have hSC : Sigma ⊆ (v '' N) ∪ (f₀ '' S₀) :=
    hgimage.subset.trans (union_subset_union_right _ (image_mono hNS₀))
  obtain ⟨p, hp, hpR, hp0, hpzero, _, hpimage⟩ := exists_boundary_cup_exterior_collar
    hc₁ hi₁ hc₁S hBS₁ htrim hf₁.continuousOn hi₁f hperiod₁ hT hf₁R hcapA hCS hSC
  obtain ⟨Z, hZ, hCZ, hcover⟩ := exists_boundary_cup_retained_core hc₁ hi₁ hS₁ hE₁
    hBS₁ hsource hED htrim htrimCover hf₁.continuousOn hi₁f hcapA hCS hpimage
  have hgO : Sigma ⊆ O := by
    intro z hz
    rcases hgimage.subset hz with hz | hz
    · rcases himage.subset hz with hz | hz
      · exact hf₁O.image_subset hz
      · obtain ⟨w, hw, rfl⟩ := hz
        exact hτO ⟨⟨hw.1.1, by rw [show w.1.2 = 1 from hw.1.2]; norm_num⟩, hw.2⟩
    · exact hf₀O.image_subset hz
  have hWA : Disjoint (v '' (c₀ '' arm (-1))) (f₁ '' S₁) := by
    rw [image_congr hkeep]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, ⟨q, hq, rfl⟩, rfl⟩ hz
    have hqEq : q = (q.1, -1) := Prod.ext rfl hq.2
    rw [hqEq, hfar₀ ⟨_, hq.1⟩] at hz
    have hh := (hA ((-1, 1), q.1) (by exact ⟨by norm_num, hq.1⟩)).mp hz
    norm_num at hh
  have hvT (x : P2) (hx : x ∈ N) : v x ∈ f₀ '' S₀ ↔ x ∈ c₀ '' arm (-1) := by
    constructor
    · intro ht
      obtain ⟨y, hy, hyx⟩ := hcapT.subset ⟨⟨x, hx, rfl⟩, ht⟩
      exact (hvi (hWN hy) hx ((hkeep hy).trans hyx)) ▸ hy
    · intro hxW
      exact ⟨x, hNS₀ hx, (hkeep hxW).symm⟩
  obtain ⟨k, hk, hki, hkR, hkO, hkv, hkA, hkT, hkproper,H,hH0,hH1,hHR,hHfront,hHfix⟩ :=
    exists_original_relative_finite_proper_disk_push_with_homotopy hR he BoundaryUnionDisk.whole_ball
      hg hgi hgR hgproper hO hgO hNball hW subset_union_right hends hv hvi
      (fun _ hx ↦ hgimage.superset (Or.inl hx))
      (hS₁.image_of_continuousOn hf₁.continuousOn).isClosed
      (hS₀.image_of_continuousOn hf₀.continuousOn).isClosed hZ hWA hCZ hvT
      p hp hpR (fun t ↦ hCS (hp0 t)) hpzero hcover
  refine ⟨v,k,hv,hvi,hkeep,hcapA,hcapT,?_,hvR,hvproper',
    hk,hki,hkR,hkO,fun x hx => (hkv hx).trans (hkeep hx),hkA,hkT,
    fun x hx => (hkproper x hx).trans (hvproper' x hx),H,hH0,hH1,hHR,hHfront,hHfix⟩
  simpa only [BoundaryCup.bridgeCoordinates_image] using himage

end PoincareConjecture.M76.Dehn.Annuli
