import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedRimRetraction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.OriginalSourceRimChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Collars.StageProperAnnulus

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

theorem PairedMarkedBoundary.exists_proper_stage_annulus
    (P : PairedMarkedBoundary L retained d)
    {T : Set (P.model.sample → ℝ × V3)} (hT : T ⊆ P.model.boundary.space)
    (hBT : ∀ b, (P.rims b).space ⊆ T)
    (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : ℝ × ℝ) = (if b then 1 else -1) ↔
        (c x : P.model.sample → ℝ × V3) ∈ (P.rims b).space) :
    ∃ k : (V1 × V2) → d.stage.Carrier,
      PolyhedralPLInCharts d.stage.charts k source ∧
      Topology.IsEmbedding (fun x : source ↦ k x) ∧
      MapsTo k source (d.stage.projection ⁻¹' chartDomain L retained) ∧
      (∀ (b : Bool) (u : Q2), k (endpoint b, u) = d.stage.annulusRim d.source_space b u) ∧
      ∀ x : source,
        k x ∈ frontier (d.stage.projection ⁻¹' chartDomain L retained) ↔
          (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  classical
  let N := P.model
  have hTK : T ⊆ N.complex.space :=
    hT.trans (SimplicialComplex.space_subset_of_le N.boundary_le)
  let radial : C(T, Q2) :=
    ⟨fun x ↦ P.radial ⟨x, hTK x.property⟩,
      P.radial.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hradial (b : Bool) (u : Q2) :
      radial ⟨P.parametrization b u, hBT b (P.parametrization b u).property⟩ = u :=
    P.radial_parametrization b u
  obtain ⟨H, hH, hHv⟩ := exists_source_chart_prescribed_rims c hc
    (fun b ↦ (P.rims b).space) hBT P.parametrization P.parametrization_PL hrim
    radial hradial
  obtain ⟨F, hF, hFv⟩ := hH
  have hFT : MapsTo F source T := by
    intro x hx
    rw [← hFv ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hFK : MapsTo F source N.complex.space := fun x hx ↦ hTK (hFT hx)
  let j : (V1 × V2) → d.stage.Carrier := fun x ↦ N.inverse (F x)
  have hj : PolyhedralPLInCharts d.stage.charts j source := by
    obtain ⟨K, hK, hKs, hKa⟩ := hF
    have hFK' : FinitePiecewiseAffineOn F K.space := ⟨K, hK, rfl, hKa⟩
    exact hKs ▸ N.inverse_PL.comp_finitePiecewiseAffineOn K hK hFK'
      (fun x hx ↦ hFK (hKs.subset hx))
  have hinv : InjOn (fun z ↦ (N.inverse z : d.stage.Carrier)) N.complex.space := by
    intro x hx y hy hxy
    have heq : N.homeomorph.symm ⟨x, hx⟩ = N.homeomorph.symm ⟨y, hy⟩ :=
      Subtype.ext ((N.inverse_value ⟨x, hx⟩).symm.trans
        (hxy.trans (N.inverse_value ⟨y, hy⟩)))
    exact congrArg Subtype.val (N.homeomorph.symm.injective heq)
  let : CompactSpace source := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
  have hjemb : Topology.IsEmbedding (fun x : source ↦ j x) := by
    apply (hj.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    apply H.injective
    apply Subtype.ext
    exact (hFv x).trans ((hinv (hFK x.property) (hFK y.property) hxy).trans (hFv y).symm)
  have hjB : MapsTo j source (frontier N.region) := by
    intro x hx
    have hmem := PoincareConjecture.M76.original_model_mem_image_iff N.homeomorph N.graph N.inverse
      N.homeomorph_value N.inverse_value N.compact.isClosed.frontier_subset ⟨F x, hFK hx⟩
    apply hmem.mpr
    rw [← N.boundary_image]
    exact hT (hFT hx)
  have hjrim (b : Bool) (u : Q2) : j (endpoint b, u) = d.stage.annulusRim d.source_space b u := by
    let x : source := ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩
    let v := d.stage.annulusRim d.source_space b u
    have hvN : v ∈ N.region := N.source_subset
      (d.stage.annulusRim_range_subset d.source_space b (mem_range_self u))
    have hFx : F x = N.graph v :=
      (hFv x).symm.trans ((hHv b u).trans (P.parametrization_value b u))
    have heq : N.homeomorph.symm ⟨F x, hFK x.property⟩ = ⟨v, hvN⟩ := by
      apply N.homeomorph.injective
      rw [N.homeomorph.apply_symm_apply]
      exact Subtype.ext (hFx.trans (N.homeomorph_value ⟨v, hvN⟩).symm)
    exact (N.inverse_value ⟨F x, hFK x.property⟩).trans (congrArg Subtype.val heq)
  exact d.stage.exists_pushed_marked_annulus d.source_space N.compact N.domain
    N.projection_subset hj hjemb hjB hjrim (fun b u ↦
      (d.frontier_iff ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b),
        u.property⟩).mpr (endpoint_mem_sphere b))

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
