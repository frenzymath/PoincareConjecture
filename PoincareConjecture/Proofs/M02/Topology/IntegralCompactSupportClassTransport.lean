import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomologyOpenMap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralCompactSupportCohomologyClass_pullback_eq_of_pushforward_eq
    [T2Space Y] (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    {K L P : Compacts X} (hKP : K ≤ P) (hLP : L ≤ P) (q : Nat)
    (a : integralSupportCohomology (f '' (K : Set X)) q)
    (b : integralSupportCohomology (f '' (L : Set X)) q)
    (h : integralSupportCohomologyPushforward (image_mono hKP) q a =
      integralSupportCohomologyPushforward (image_mono hLP) q b) :
    integralCompactSupportCohomologyClass K q
        ((integralSupportOpenEmbeddingCohomologyIso f hf K q).hom a) =
      integralCompactSupportCohomologyClass L q
        ((integralSupportOpenEmbeddingCohomologyIso f hf L q).hom b) := by
  apply (integralCompactSupportCohomologyClass_eq_iff _ _).mpr
  refine ⟨P, hKP, hLP, ?_⟩
  have hK := congrArg (fun g => g a)
    (integralSupportOpenEmbeddingCohomologyIso_naturality f hf hKP q)
  have hL := congrArg (fun g => g b)
    (integralSupportOpenEmbeddingCohomologyIso_naturality f hf hLP q)
  exact hK.symm.trans
    ((congrArg (integralSupportOpenEmbeddingCohomologyIso f hf P q).hom h).trans hL)

theorem integralCompactSupportCohomologyClass_eq_of_openEmbedding_pushforward_eq
    [T2Space Y] (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    {K L P : Compacts X} (hKP : K ≤ P) (hLP : L ≤ P) (q : Nat)
    (a : integralSupportCohomology (K : Set X) q)
    (b : integralSupportCohomology (L : Set X) q)
    (h : integralSupportCohomologyPushforward (image_mono hKP) q
        ((integralSupportOpenEmbeddingCohomologyIso f hf K q).inv a) =
      integralSupportCohomologyPushforward (image_mono hLP) q
        ((integralSupportOpenEmbeddingCohomologyIso f hf L q).inv b)) :
    integralCompactSupportCohomologyClass K q a =
      integralCompactSupportCohomologyClass L q b := by
  have hEq := integralCompactSupportCohomologyClass_pullback_eq_of_pushforward_eq
    f hf hKP hLP q _ _ h
  have hK : (integralSupportOpenEmbeddingCohomologyIso f hf K q).hom
      ((integralSupportOpenEmbeddingCohomologyIso f hf K q).inv a) = a := by
    change ((integralSupportOpenEmbeddingCohomologyIso f hf K q).inv ≫
      (integralSupportOpenEmbeddingCohomologyIso f hf K q).hom) a = a
    rw [Iso.inv_hom_id]
    rfl
  have hL : (integralSupportOpenEmbeddingCohomologyIso f hf L q).hom
      ((integralSupportOpenEmbeddingCohomologyIso f hf L q).inv b) = b := by
    change ((integralSupportOpenEmbeddingCohomologyIso f hf L q).inv ≫
      (integralSupportOpenEmbeddingCohomologyIso f hf L q).hom) b = b
    rw [Iso.inv_hom_id]
    rfl
  rwa [hK, hL] at hEq

end PoincareConjecture.Proofs.M02.Topology
