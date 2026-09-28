import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComponentCochainExactness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.IncidenceRanks



set_option autoImplicit false
open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace LinearMap

theorem finrank_quotient_bound_of_surjective
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (F : V →ₗ[k] W) (hF : Function.Surjective F)
    (B : Submodule k V) (D : Submodule k W) (hBD : B ≤ D.comap F) :
    Module.finrank k W + Module.finrank k B ≤
      Module.finrank k V + Module.finrank k D := by
  let q := B.mapQ D F hBD
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, rfl⟩ := D.mkQ_surjective y
    obtain ⟨v, rfl⟩ := hF w
    exact ⟨B.mkQ v, rfl⟩
  have hle := LinearMap.finrank_le_finrank_of_surjective hq
  have hB := B.finrank_quotient_add_finrank
  have hD := D.finrank_quotient_add_finrank
  omega

end LinearMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A B : SimplicialComplex ℝ E)
  [Fintype K.vertices] [Fintype A.vertices] [Fintype B.vertices]

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "BA" => B.vertexAbstractComplex.toPreAbstractSimplicialComplex

open Classical in
theorem closed_subcomplex_rank_bound
    (hAK : A ≤ K)
    (hAc : ∀ {s t : Finset E}, s ∈ A.faces → t ∈ K.faces → s ⊆ t → t ∈ A.faces) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA)) +
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) +
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary AA)) := by
  classical
  let ZK := LinearMap.ker (edgeCoboundary KA)
  let ZA := LinearMap.ker (edgeCoboundary AA)
  let iA := K.subcomplexFaceEmbedding A hAK 2
  let F : ZK →ₗ[ZMod 2] ZA := {
    toFun := fun z ↦ ⟨z.val ∘ iA, by
      rw [LinearMap.mem_ker, K.edgeCoboundary_subcomplex_restrict A hAK]
      exact funext (fun t ↦ congrFun z.property (K.subcomplexFaceEmbedding A hAK 3 t))⟩
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hF : Function.Surjective F := by
    intro a
    refine ⟨⟨Function.extend iA a.val 0,
      K.edgeCoboundary_zeroExtend_of_closed_cofaces A hAK hAc _ a.property⟩, ?_⟩
    exact Subtype.ext (funext (fun e ↦ iA.injective.extend_apply _ _ e))
  let CK := (LinearMap.range (vertexCoboundary KA)).comap ZK.subtype
  let CA := (LinearMap.range (vertexCoboundary AA)).comap ZA.subtype
  have hCAK : CK ≤ CA.comap F := by
    rintro z ⟨v, hv⟩
    exact ⟨v ∘ K.subcomplexVertexEmbedding A hAK,
      (K.vertexCoboundary_subcomplex_restrict A hAK v).trans (congrArg (· ∘ iA) hv)⟩
  have hle := F.finrank_quotient_bound_of_surjective hF CK CA hCAK
  have hCK := (Submodule.comapSubtypeEquivOfLe
    (show LinearMap.range (vertexCoboundary KA) ≤ ZK by
      rintro _ ⟨v, rfl⟩; exact edgeCoboundary_vertexCoboundary KA v)).finrank_eq
  have hCA := (Submodule.comapSubtypeEquivOfLe
    (show LinearMap.range (vertexCoboundary AA) ≤ ZA by
      rintro _ ⟨v, rfl⟩; exact edgeCoboundary_vertexCoboundary AA v)).finrank_eq
  change Module.finrank (ZMod 2) CK = _ at hCK
  change Module.finrank (ZMod 2) CA = _ at hCA
  rw [hCK, hCA] at hle
  exact hle

open Classical in
theorem disjoint_closed_subcomplex_rank_bound
    (hAK : A ≤ K) (hBK : B ≤ K) (hdis : Disjoint A.space B.space)
    (hAc : ∀ {s t : Finset E}, s ∈ A.faces → t ∈ K.faces → s ⊆ t → t ∈ A.faces)
    (hBc : ∀ {s t : Finset E}, s ∈ B.faces → t ∈ K.faces → s ⊆ t → t ∈ B.faces) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA)) +
        Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary BA)) +
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) +
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary AA)) +
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary BA)) := by
  classical
  let ZK := LinearMap.ker (edgeCoboundary KA)
  let ZA := LinearMap.ker (edgeCoboundary AA)
  let ZB := LinearMap.ker (edgeCoboundary BA)
  let iA := K.subcomplexFaceEmbedding A hAK 2
  let iB := K.subcomplexFaceEmbedding B hBK 2
  have hi (a : Edge AA) (b : Edge BA) : iA a ≠ iB b := by
    intro hab
    have he := congrArg (fun e : Edge KA ↦ e.val.map (Function.Embedding.subtype _)) hab
    change (K.subcomplexFaceEmbedding A hAK 2 a).val.map _ =
      (K.subcomplexFaceEmbedding B hBK 2 b).val.map _ at he
    rw [K.subcomplexFaceEmbedding_forget, K.subcomplexFaceEmbedding_forget] at he
    obtain ⟨v, hv⟩ := A.nonempty_of_mem_faces a.property.1
    exact Set.disjoint_left.mp hdis
      (A.convexHull_subset_space a.property.1 (subset_convexHull ℝ _ hv))
      (B.convexHull_subset_space b.property.1 (subset_convexHull ℝ _ (he ▸ hv)))
  let F : ZK →ₗ[ZMod 2] ZA × ZB := {
    toFun := fun z ↦
      (⟨z.val ∘ iA, by
        rw [LinearMap.mem_ker, K.edgeCoboundary_subcomplex_restrict A hAK]
        exact funext (fun t ↦ congrFun z.property (K.subcomplexFaceEmbedding A hAK 3 t))⟩,
       ⟨z.val ∘ iB, by
        rw [LinearMap.mem_ker, K.edgeCoboundary_subcomplex_restrict B hBK]
        exact funext (fun t ↦ congrFun z.property (K.subcomplexFaceEmbedding B hBK 3 t))⟩)
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hF : Function.Surjective F := by
    rintro ⟨a, b⟩
    let za := Function.extend iA a.val 0
    let zb := Function.extend iB b.val 0
    have hza : za ∈ ZK := K.edgeCoboundary_zeroExtend_of_closed_cofaces A hAK hAc _ a.property
    have hzb : zb ∈ ZK := K.edgeCoboundary_zeroExtend_of_closed_cofaces B hBK hBc _ b.property
    refine ⟨⟨za + zb, ZK.add_mem hza hzb⟩, ?_⟩
    apply Prod.ext <;> apply Subtype.ext <;> funext e
    · change za (iA e) + zb (iA e) = a.val e
      rw [show za (iA e) = a.val e from iA.injective.extend_apply _ _ e]
      have hz : zb (iA e) = 0 := Function.extend_apply' (f := (iB : Edge BA → Edge KA))
        b.val (0 : Edge KA → ZMod 2) _
        (by rintro ⟨q, hq⟩; exact hi e q hq.symm)
      rw [hz, add_zero]
    · change za (iB e) + zb (iB e) = b.val e
      rw [show zb (iB e) = b.val e from iB.injective.extend_apply _ _ e]
      have hz : za (iB e) = 0 := Function.extend_apply' (f := (iA : Edge AA → Edge KA))
        a.val (0 : Edge KA → ZMod 2) _
        (by rintro ⟨q, hq⟩; exact hi q e hq)
      rw [hz, zero_add]
  let CK := (LinearMap.range (vertexCoboundary KA)).comap ZK.subtype
  let CA := (LinearMap.range (vertexCoboundary AA)).comap ZA.subtype
  let CB := (LinearMap.range (vertexCoboundary BA)).comap ZB.subtype
  have hBD : CK ≤ (CA.prod CB).comap F := by
    rintro z ⟨v, hv⟩
    constructor
    · exact ⟨v ∘ K.subcomplexVertexEmbedding A hAK,
        (K.vertexCoboundary_subcomplex_restrict A hAK v).trans (congrArg (· ∘ iA) hv)⟩
    · exact ⟨v ∘ K.subcomplexVertexEmbedding B hBK,
        (K.vertexCoboundary_subcomplex_restrict B hBK v).trans (congrArg (· ∘ iB) hv)⟩
  have hle := F.finrank_quotient_bound_of_surjective hF CK (CA.prod CB) hBD
  have hCK := (Submodule.comapSubtypeEquivOfLe
    (show LinearMap.range (vertexCoboundary KA) ≤ ZK by
      rintro _ ⟨v, rfl⟩; exact edgeCoboundary_vertexCoboundary KA v)).finrank_eq
  have hCA := (Submodule.comapSubtypeEquivOfLe
    (show LinearMap.range (vertexCoboundary AA) ≤ ZA by
      rintro _ ⟨v, rfl⟩; exact edgeCoboundary_vertexCoboundary AA v)).finrank_eq
  have hCB := (Submodule.comapSubtypeEquivOfLe
    (show LinearMap.range (vertexCoboundary BA) ≤ ZB by
      rintro _ ⟨v, rfl⟩; exact edgeCoboundary_vertexCoboundary BA v)).finrank_eq
  let pe : (CA.prod CB) ≃ₗ[ZMod 2] CA × CB := {
    toFun := fun x ↦ (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
    invFun := fun x ↦ ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hprod := pe.finrank_eq
  simp only [Module.finrank_prod] at hprod hle
  change Module.finrank (ZMod 2) CK = _ at hCK
  change Module.finrank (ZMod 2) CA = _ at hCA
  change Module.finrank (ZMod 2) CB = _ at hCB
  rw [hprod, hCK, hCA, hCB] at hle
  dsimp only [ZK, ZA, ZB] at hle
  omega

end Geometry.SimplicialComplex
