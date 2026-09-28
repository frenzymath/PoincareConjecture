import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.TubeModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.NormalizedSignedTubeMap

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "tubeSet" => PolygonalCrossingResolution.tube

theorem OrdinaryDoubleCurveModel.exists_normalized_interval_tube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index)
    (hball : IsFinitePLBallPair ℝ (old.pieces i) (old.pieces i ∩ Q2))
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) :
    ∃ D : OrdinaryIntervalMarkedModel old i,
      letI : ∀ j, Fintype (D.marks j).faces := fun j ↦ (D.marks_full j).2.1.fintype
      ∃ (a : I01 ≃ₜ old.pieces i) (b : I01 ≃ₜ (D.marks (.inr 2)).space)
        (sigma : C3 → (D.sample → ℝ × V3)) (τ : C3 → X),
        a.IsFinitePL ∧ b.IsFinitePL ∧
        (∀ t : I01, (b t : D.sample → ℝ × V3) = D.graph (f (a t))) ∧
        τ = (fun z ↦ (D.inverse z : X)) ∘ sigma ∧
        FinitePiecewiseAffineOn sigma tubeSet ∧ InjOn sigma tubeSet ∧
        sigma '' tubeSet = ((D.marks (.inl false)).barycentricNeighborhood
          (D.marks (.inr 2))).space ∧
        MapsTo sigma tubeSet D.complex.space ∧
        (∀ t : I01, sigma ((0, 0), t) = b t) ∧
        (∀ j : Fin 2, ∀ z ∈ tubeSet,
          sigma z ∈ (D.marks (.inr j.castSucc)).space ↔
            z.1.2 = if j = 0 then z.1.1 else -z.1.1) ∧
        (∀ z ∈ tubeSet, sigma z ∈ (D.marks (.inl true)).space ↔ z.2 = 0 ∨ z.2 = 1) ∧
        PolyhedralPLInCharts e τ tubeSet ∧ InjOn τ tubeSet ∧ MapsTo τ tubeSet R ∧
        τ '' tubeSet = (fun z ↦ (D.inverse z : X)) ''
          ((D.marks (.inl false)).barycentricNeighborhood (D.marks (.inr 2))).space ∧
        (∀ t : I01, τ ((0, 0), t) = f (a t)) ∧
        (∀ j : Fin 2, ∀ z ∈ tubeSet,
          τ z ∈ f '' (D.source j.castSucc).space ↔
            z.1.2 = if j = 0 then z.1.1 else -z.1.1) ∧
        (∀ j : Fin 2, ∀ z ∈ tubeSet,
          τ z ∈ f '' (D.clips j.castSucc).space ↔
            z.1.2 = if j = 0 then z.1.1 else -z.1.1) ∧
        (∀ z ∈ tubeSet, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) ∧
        τ '' tubeSet ⊆ D.core ∧
        (∀ x ∈ D2, f x ∈ τ '' tubeSet →
          x ∈ (D.source 0).space ∪ (D.source 1).space) ∧
        ∀ x ∈ D2, f x ∈ τ '' tubeSet →
          x ∈ (D.clips 0).space ∪ (D.clips 1).space := by
  classical
  obtain ⟨D, hD⟩ := old.exists_interval_tube_model hf he i hball hin hfront
  let _ : ∀ j, Fintype (D.marks j).faces := fun j ↦ (D.marks_full j).2.1.fintype
  obtain ⟨a, b, tube, ha, hb, htube, hbval, hgb, haxis, hsheet, hends⟩ := hD
  obtain ⟨sigma, hsigma, hsigmai, hsigmaimage, hsigmaaxis, hsigmasheet, hsigmaends⟩ :=
    exists_normalized_signed_tube_map
      (fun j : Fin 2 ↦ (D.marks (.inr j.castSucc)).space)
      tube htube (fun t ↦ (b t : D.sample → ℝ × V3)) haxis hsheet hends
  let τ : C3 → X := (fun z ↦ (D.inverse z : X)) ∘ sigma
  have hNR : ((D.marks (.inl false)).barycentricNeighborhood
      (D.marks (.inr 2))).space ⊆ (D.marks (.inl false)).space := by
    intro z hz
    have h := SimplicialComplex.space_subset_of_le
      ((D.marks (.inl false)).barycentricNeighborhood_le (D.marks (.inr 2))) hz
    rwa [(D.marks (.inl false)).barycentricSubdivision_isSubdivision.space_eq] at h
  have hsigmaR : MapsTo sigma tubeSet (D.marks (.inl false)).space :=
    fun z hz ↦ hNR (hsigmaimage.subset (mem_image_of_mem sigma hz))
  have hsigmaK : MapsTo sigma tubeSet D.complex.space := fun z hz ↦
    SimplicialComplex.space_subset_of_le (D.marks_full (.inl false)).1 (hsigmaR hz)
  have hτPL : PolyhedralPLInCharts e τ tubeSet := by
    obtain ⟨L, hL, hLs, hsigmaaff⟩ := hsigma
    have h := D.inverse_PL.comp_finitePiecewiseAffineOn L hL
      (show FinitePiecewiseAffineOn sigma L.space from ⟨L, hL, rfl, hsigmaaff⟩)
      (show MapsTo sigma L.space D.complex.space from hLs.symm ▸ hsigmaK)
    exact hLs ▸ h
  have hτi : InjOn τ tubeSet := by
    intro x hx y hy hxy
    apply hsigmai hx hy
    have h := congrArg D.graph hxy
    change D.graph (D.inverse (sigma x)) = D.graph (D.inverse (sigma y)) at h
    rwa [D.graph_inverse _ (hsigmaK hx), D.graph_inverse _ (hsigmaK hy)] at h
  have hτR : MapsTo τ tubeSet R := fun z hz ↦
    (D.mem_mark_image D.region_image (sigma z) (hsigmaK hz)).mp (hsigmaR hz)
  have hτimage : τ '' tubeSet = (fun z ↦ (D.inverse z : X)) ''
      ((D.marks (.inl false)).barycentricNeighborhood (D.marks (.inr 2))).space := by
    rw [← hsigmaimage, ← image_comp]
  have hτC : τ '' tubeSet ⊆ D.core := by
    rintro _ ⟨z, _, rfl⟩
    exact (D.inverse (sigma z)).property
  have hτsheet (j : Fin 2) (z : C3) (hz : z ∈ tubeSet) :
      τ z ∈ f '' (D.source j.castSucc).space ↔
        z.1.2 = if j = 0 then z.1.1 else -z.1.1 :=
    (D.mem_mark_image (D.marks_image j.castSucc) (sigma z) (hsigmaK hz)).symm.trans
      (hsigmasheet j z hz)
  have hτclip (j : Fin 2) (z : C3) (hz : z ∈ tubeSet) :
      τ z ∈ f '' (D.clips j.castSucc).space ↔
        z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
    rw [← hτsheet j z hz, (D.clips_data j.castSucc).2.1]
    constructor
    · exact fun h ↦ image_mono inter_subset_left h
    · rintro ⟨x, hx, hfx⟩
      have hxC : f x ∈ D.core := hfx.symm ▸
        (show τ z ∈ D.core from (D.inverse (sigma z)).property)
      exact ⟨x, ⟨hx, hxC⟩, hfx⟩
  have hτends (z : C3) (hz : z ∈ tubeSet) :
      τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 :=
    (D.mem_mark_image D.frontier_image (sigma z) (hsigmaK hz)).symm.trans (hsigmaends z hz)
  have hpre (x : V2) (hx : x ∈ D2) (hfx : f x ∈ τ '' tubeSet) :
      x ∈ (D.source 0).space ∪ (D.source 1).space :=
    D.full_preimage x hx (D.core_subset (hτC hfx))
  refine ⟨D, a, b, sigma, τ, ha, hb, hbval, rfl, hsigma, hsigmai, hsigmaimage, hsigmaK,
    hsigmaaxis, hsigmasheet, hsigmaends, hτPL, hτi, hτR, hτimage, ?_, hτsheet, hτclip,
    hτends, hτC, hpre, ?_⟩
  · intro t
    change (D.inverse (sigma ((0, 0), t)) : X) = f (a t)
    rw [hsigmaaxis]
    exact hgb t
  · intro x hx hfx
    rw [(D.clips_data 0).2.1, (D.clips_data 1).2.1]
    exact (hpre x hx hfx).elim (fun h ↦ Or.inl ⟨h, hτC hfx⟩)
      (fun h ↦ Or.inr ⟨h, hτC hfx⟩)

end PoincareConjecture.M76.Dehn
