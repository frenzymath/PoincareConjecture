import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {I W : Type u} [TopologicalSpace I] [TopologicalSpace W]

theorem integralCompactSupportCohomologyClass_of_compact_range [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f) (q : Nat)
    (c : integralSupportCohomology (R : Set W) q) :
    ∃ (S : Compacts I) (d : integralSupportCohomology (S : Set I) q),
      (integralCompactSupportCohomologyClass S q ≫
          integralCompactSupportCohomologyOpenMap f hf q) d =
        (integralCompactSupportCohomologyClass R q) c := by
  let S : Compacts I :=
    ⟨f ⁻¹' (R : Set W), hf.isEmbedding.isCompact_preimage' R.isCompact hR⟩
  have hSR : S.map f f.continuous = R := by
    apply Compacts.ext
    exact image_preimage_eq_of_subset hR
  let e := integralSupportOpenEmbeddingCohomologyIso f hf S q
  let c' : integralSupportCohomology ((S.map f f.continuous : Compacts W) : Set W) q :=
    hSR.symm ▸ c
  let d : integralSupportCohomology (S : Set I) q := e.hom c'
  refine ⟨S, d, ?_⟩
  have hc := integralCompactSupportCohomologyOpenMap_class f hf S q
  have he := congrArg (fun g => g d) hc
  change (integralCompactSupportCohomologyClass S q ≫
      integralCompactSupportCohomologyOpenMap f hf q) d = _ at he
  rw [he]
  change (integralCompactSupportCohomologyClass (S.map f f.continuous) q) (e.inv d) = _
  have hcd : e.inv d = c' := by
    change (e.hom ≫ e.inv) c' = c'
    rw [e.hom_inv_id]
    rfl
  rw [hcd]
  have transport (R T : Compacts W) (h : T = R)
      (c : integralSupportCohomology (R : Set W) q) :
      (integralCompactSupportCohomologyClass T q) (h.symm ▸ c) =
        (integralCompactSupportCohomologyClass R q) c := by
    subst T
    rfl
  exact transport R (S.map f f.continuous) hSR c

theorem exists_integralSupportCohomology_preimage_of_compact_range [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f) (q : Nat)
    (c : integralSupportCohomology (R : Set W) q) :
    ∃ (S : Compacts I) (d : integralSupportCohomology (S : Set I) q),
      ∃ hSR : S.map f f.continuous = R,
        (integralSupportOpenEmbeddingCohomologyIso f hf S q).inv d =
          Eq.mp (congrArg (fun K : Compacts W =>
            (integralSupportCohomology (K : Set W) q : Type u)) hSR.symm) c := by
  let S : Compacts I :=
    ⟨f ⁻¹' (R : Set W), hf.isEmbedding.isCompact_preimage' R.isCompact hR⟩
  have hSR : S.map f f.continuous = R := by
    apply Compacts.ext
    exact image_preimage_eq_of_subset hR
  let e := integralSupportOpenEmbeddingCohomologyIso f hf S q
  let hType : (integralSupportCohomology (R : Set W) q : Type u) =
      (integralSupportCohomology ((S.map f f.continuous : Compacts W) : Set W) q : Type u) :=
    congrArg (fun K : Compacts W => (integralSupportCohomology (K : Set W) q : Type u)) hSR.symm
  let c' : integralSupportCohomology ((S.map f f.continuous : Compacts W) : Set W) q :=
    cast hType c
  let d : integralSupportCohomology (S : Set I) q := e.hom c'
  refine ⟨S, d, hSR, ?_⟩
  change (e.hom ≫ e.inv) c' = cast hType c
  rw [e.hom_inv_id]
  rfl

end Poincare.Topology
