import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereSubregionModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereSubregionSpheres

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Cube" => closedBall (0 : V3) 1

theorem PLDomain.exists_punctured_subregion_model
    {X E ι κ ν : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] [Finite ν]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X} {M : Set E}
    (hD : PLDomain e D) (hDc : IsConnected D) (hDR : D ⊆ R)
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hAo : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A i \ r i)))
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (G : R ≃ₜ M) (hG : ∀ x : R, (G x : E) = f x)
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier D = ⋃ i, S i) :
    let T := fun i => (fun x : R => (C (G x) : V4)) ''
      ((Subtype.val : R → X) ⁻¹' S i)
    ∃ B : ν → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (T i) ∧ B i ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ T i))) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (fun x : R => (C (G x) : V4)) '' ((Subtype.val : R → X) ⁻¹' interior D) =
        Sphere \ ⋃ i, B i ∧
      (fun x : R => (C (G x) : V4)) '' ((Subtype.val : R → X) ⁻¹' D) =
        Sphere \ ⋃ i, B i \ T i ∧
      ∃ H : D ≃ₜ (Sphere \ ⋃ i, B i \ T i : Set V4),
        ∀ x : D, (H x : V4) = C (G ⟨x, hDR x.property⟩) := by
  classical
  let Q : Set V4 := Sphere \ ⋃ i, A i \ r i
  let Qr : Set Sphere := (Subtype.val : Sphere → V4) ⁻¹' Q
  let q : R → V4 := fun x => C (G x)
  let T : ν → Set V4 := fun i => q '' ((Subtype.val : R → X) ⁻¹' S i)
  have hQS : Q ⊆ Sphere := sdiff_subset
  obtain ⟨hQr, _, hQfront⟩ :=
    Geometry.CubicalThreeSphere.punctured_sphere_relative_geometry A r hA hAS hAdis hAo
  change IsClosed Qr at hQr
  change frontier Qr = (Subtype.val : Sphere → V4) ⁻¹' (⋃ i, r i) at hQfront
  let J : Qr ≃ₜ Q := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by simpa only [Subtype.range_coe] using hQS)
  let H : R ≃ₜ Qr := G.trans (C.trans J.symm)
  have hHv (x : R) : ((H x : Qr) : Sphere).val = q x := by
    change (J (J.symm (C (G x))) : V4) = (C (G x) : V4)
    rw [J.apply_symm_apply]
  have hHmark : ∀ x : R, (x : X) ∈ frontier R ↔ (H x : Sphere) ∈ frontier Qr := by
    intro x
    rw [hQfront]
    change (x : X) ∈ frontier R ↔ ((H x : Qr) : Sphere).val ∈ ⋃ i, r i
    rw [hHv]
    exact hmark x
  let P : Set Sphere := (Subtype.val : Qr → Sphere) ''
    (H '' ((Subtype.val : R → X) ⁻¹' D))
  have hPclosed : IsClosed P := hQr.isClosedMap_subtype_val _
    (H.isClosedMap _ (hD.closed.preimage continuous_subtype_val))
  have hint : interior P = (Subtype.val : Qr → Sphere) ''
      (H '' ((Subtype.val : R → X) ⁻¹' interior D)) :=
    H.interior_image_subdomain hHmark hDR
  have hcl : closure (interior P) = P := by
    have hclsub : closure (interior D) ⊆ R := by rw [hD.closure_interior]; exact hDR
    rw [hint, H.closure_image_subdomain hQr hclsub, hD.closure_interior]
  have hIc : IsConnected (interior P) := by
    have hsource : IsConnected ((Subtype.val : R → X) ⁻¹' interior D) := by
      refine ⟨?_, ?_⟩
      · obtain ⟨x, hx⟩ := (hD.isConnected_interior hDc).nonempty
        exact ⟨⟨x, hDR (interior_subset hx)⟩, hx⟩
      · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        rw [image_preimage_eq_of_subset (by
          simpa only [Subtype.range_coe] using (interior_subset.trans hDR : interior D ⊆ R))]
        exact (hD.isConnected_interior hDc).isPreconnected
    rw [hint]
    exact (hsource.image H H.continuous.continuousOn).image Subtype.val
      continuous_subtype_val.continuousOn
  have hfrontP : frontier (interior P) =
      (Subtype.val : Qr → Sphere) '' (H '' ((Subtype.val : R → X) ⁻¹' frontier D)) := by
    have hh : frontier (interior P) = frontier P := by
      rw [frontier, hcl, interior_interior, hPclosed.frontier_eq]
    exact hh.trans (H.frontier_image_subdomain hQr hD.closed hHmark hDR)
  have hSR (i : ν) : S i ⊆ R :=
    (subset_iUnion S i).trans (hfront.symm.subset.trans (hD.closed.frontier_subset.trans hDR))
  have hqinj : Function.Injective q := by
    intro x y hxy
    exact G.injective (C.injective (Subtype.ext hxy))
  have hTdis : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x, hxi, hxz⟩ ⟨y, hyj, hyz⟩
    have hxy := hqinj (hxz.trans hyz.symm)
    subst y
    exact disjoint_left.mp (hSdis hij) hxi hyj
  have hTS (i : ν) : T i ⊆ Sphere := by
    rintro _ ⟨x, _, rfl⟩
    exact (C (G x)).property.1
  have hTparam (i : ν) : ∃ d : T i ≃ₜ frontier Cube, d.IsFinitePL :=
    (sS i).exists_finitePL_parent_model_image (hSR i) f hf G hG C hC
  choose d hd using hTparam
  have hfrontT : frontier (interior P) = ⋃ i, (Subtype.val : Sphere → V4) ⁻¹' T i := by
    rw [hfrontP, hfront]
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, ⟨x, hxi, (hHv x).symm⟩⟩
    · intro hz
      obtain ⟨i, x, hxi, hxz⟩ := mem_iUnion.mp hz
      refine ⟨H x, ⟨x, mem_iUnion.mpr ⟨i, hxi⟩, rfl⟩, ?_⟩
      exact Subtype.ext ((hHv x).trans hxz)
  obtain ⟨B, hB, hBdis, hBI, hBP⟩ := Set.exists_punctured_sphere_of_spherical_frontier
    T d hd hTS hTdis isOpen_interior hIc hfrontT
  have himage (W : Set X) : (Subtype.val : Sphere → V4) ''
      ((Subtype.val : Qr → Sphere) '' (H '' ((Subtype.val : R → X) ⁻¹' W))) =
      q '' ((Subtype.val : R → X) ⁻¹' W) := by
    rw [image_image, image_image]
    congr 1
    funext x
    exact hHv x
  rw [hint, himage] at hBI
  rw [hcl] at hBP
  change (Subtype.val : Sphere → V4) '' P = _ at hBP
  rw [show P = (Subtype.val : Qr → Sphere) ''
    (H '' ((Subtype.val : R → X) ⁻¹' D)) from rfl, himage] at hBP
  refine ⟨B, hB, hBdis, hBI, hBP, ?_⟩
  let I : ((Subtype.val : R → X) ⁻¹' D) ≃ₜ D :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe] using hDR)
  have hqemb : Topology.IsEmbedding q :=
    Topology.IsEmbedding.subtypeVal.comp (C.isEmbedding.comp G.isEmbedding)
  let model := I.symm.trans ((hqemb.homeomorphImage ((Subtype.val : R → X) ⁻¹' D)).trans
    (Homeomorph.setCongr hBP))
  refine ⟨model, fun x => ?_⟩
  change q (I.symm x) = q ⟨x, hDR x.property⟩
  have hIx : ((I.symm x : R) : X) = (x : X) :=
    congrArg (fun y : D => (y : X)) (I.apply_symm_apply x)
  exact congrArg q (show (I.symm x : R) = ⟨x, hDR x.property⟩ from Subtype.ext hIx)

end PoincareConjecture.M76
