import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.AnnulusSelection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.SourceRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Collars.StageProperAnnulus

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

open Poincare.Topology.Orientation.ProjectivePlane

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → X}
  {r : X → ℝ} {C R : Set X} {st : Stage e S g r C} {F : Bool → Set X}

theorem MarkedBoundaryPair.exists_proper_stage_annulus_of_localOrientation
    (P : MarkedBoundaryPair st R F) (O : LocalOrientation st.Carrier) (hF : ∀ b, F b ⊆ frontier R) :
    ∃ (k : (V1 × V2) → st.Carrier) (f : C(ProtectedAnnulus.source, R)),
      PolyhedralPLInCharts st.charts k ProtectedAnnulus.source ∧
      Topology.IsEmbedding (fun x : ProtectedAnnulus.source ↦ k x) ∧
      (∀ x : ProtectedAnnulus.source, (f x : X) = st.projection (k x)) ∧
      (∀ (b : Bool) (u : Q2), st.projection (k (ProtectedAnnulus.endpoint b, u)) ∈ F b) ∧
      (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
      ∀ x : ProtectedAnnulus.source,
        k x ∈ frontier (st.projection ⁻¹' R) ↔
          (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  classical
  obtain ⟨T, c, hT, hc, hBT, hrim⟩ := P.exists_boundary_annulus_of_localOrientation O
  obtain ⟨H, q, hH, hHv⟩ := ProtectedAnnulus.exists_source_chart_comparison_rims c hc
    (fun b ↦ (P.rims b).space) hBT P.parametrization hrim
  let N := P.model
  have hTK : T ⊆ N.complex.space :=
    hT.trans (SimplicialComplex.space_subset_of_le N.boundary_le)
  obtain ⟨a, ha, hav⟩ := hH
  have haT : MapsTo a ProtectedAnnulus.source T := by
    intro x hx
    rw [← hav ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have haK : MapsTo a ProtectedAnnulus.source N.complex.space := fun x hx ↦ hTK (haT hx)
  let j : (V1 × V2) → st.Carrier := fun x ↦ N.inverse (a x)
  have hj : PolyhedralPLInCharts st.charts j ProtectedAnnulus.source := by
    obtain ⟨K, hK, hKs, hKa⟩ := ha
    exact hKs ▸ N.inverse_PL.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hKa⟩
      (fun x hx ↦ haK (hKs.subset hx))
  have hinv : InjOn (fun z ↦ (N.inverse z : st.Carrier)) N.complex.space := by
    intro x hx y hy hxy
    have heq : N.homeomorph.symm ⟨x, hx⟩ = N.homeomorph.symm ⟨y, hy⟩ :=
      Subtype.ext ((N.inverse_value ⟨x, hx⟩).symm.trans
        (hxy.trans (N.inverse_value ⟨y, hy⟩)))
    exact congrArg Subtype.val (N.homeomorph.symm.injective heq)
  let : CompactSpace ProtectedAnnulus.source := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
  have hjemb : Topology.IsEmbedding (fun x : ProtectedAnnulus.source ↦ j x) := by
    apply (hj.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    apply H.injective
    apply Subtype.ext
    exact (hav x).trans ((hinv (haK x.property) (haK y.property) hxy).trans (hav y).symm)
  have hjB : MapsTo j ProtectedAnnulus.source (frontier N.region) := by
    intro x hx
    apply (PoincareConjecture.M76.original_model_mem_image_iff N.homeomorph N.graph N.inverse
      N.homeomorph_value N.inverse_value N.compact.isClosed.frontier_subset ⟨a x, haK hx⟩).mpr
    rw [← N.boundary_image]
    exact hT (haT hx)
  have hjrim (b : Bool) (u : Q2) :
      st.projection (j (ProtectedAnnulus.endpoint b, u)) =
        (N.originalProjection (P.boundaryRim_generic b (q b u)) : X) := by
    let x : ProtectedAnnulus.source := ⟨(ProtectedAnnulus.endpoint b, u),
      sphere_subset_closedBall (ProtectedAnnulus.endpoint_mem_sphere b), u.property⟩
    have havalue : a x = (P.parametrization b (q b u) : N.sample → ℝ × V3) :=
      (hav x).symm.trans (hHv b u)
    change st.projection (N.inverse (a x)) = _
    rw [havalue]
    exact congrArg st.projection (N.inverse_value
      ⟨P.parametrization b (q b u), SimplicialComplex.space_subset_of_le
        ((P.rim_le b).trans N.boundary_le) (P.parametrization b (q b u)).property⟩)
  obtain ⟨k, hk, hki, hkN, _, hproper, hfix⟩ :=
    ProtectedAnnulus.exists_original_annulus_push N.compact N.domain hj hjemb hjB
  let f : C(ProtectedAnnulus.source, R) := {
    toFun := fun x ↦ ⟨st.projection (k x), N.projection_subset (hkN x.property)⟩
    continuous_toFun := (st.projection.continuous.comp hk.continuousOn.domRestrict).subtype_mk _ }
  have hkrim (b : Bool) (u : Q2) : st.projection (k (ProtectedAnnulus.endpoint b, u)) =
      (N.originalProjection (P.boundaryRim_generic b (q b u)) : X) := by
    rw [hfix]
    exact hjrim b u
  have hmark (b : Bool) (u : Q2) : st.projection (k (ProtectedAnnulus.endpoint b, u)) ∈ F b := by
    rw [hkrim]
    exact P.marked b (q b u)
  refine ⟨k, f, hk, hki, fun _ ↦ rfl, hmark, ?_, ?_⟩
  · intro b hn
    have hback : (sourceAnnulusRim f b).comp ((q b).symm : C(Q2, Q2)) =
        N.originalProjection.comp (P.boundaryRim_generic b) := by
      apply ContinuousMap.ext
      intro u
      apply Subtype.ext
      change st.projection (k (ProtectedAnnulus.endpoint b, (q b).symm u)) = _
      rw [hkrim, (q b).apply_symm_apply]
      rfl
    exact P.essential b (hback ▸ hn.comp_left ((q b).symm : C(Q2, Q2)))
  · intro x
    constructor
    · intro hf
      by_contra hx
      have hxN : k x ∈ interior N.region :=
        (mem_interior_iff_notMem_frontier (hkN x.property)).mpr
          (fun h ↦ hx ((hproper x).mp h).1)
      exact hf.2 (interior_mono N.projection_subset hxN)
    · intro hx
      obtain ⟨b, hb⟩ := (ProtectedAnnulus.mem_sphere_iff_exists_endpoint _).mp hx
      have hpair : (x : V1 × V2) = (ProtectedAnnulus.endpoint b, (x : V1 × V2).2) :=
        Prod.ext hb rfl
      rw [st.frontier_region R]
      change st.projection (k x) ∈ frontier R
      rw [hpair]
      exact hF b (hmark b ⟨(x : V1 × V2).2, x.property.2⟩)

end Geometry.OriginalPLTower
