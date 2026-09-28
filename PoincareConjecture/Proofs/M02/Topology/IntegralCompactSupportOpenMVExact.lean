import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMVRepresentatives
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMVTail
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCohomologyLifting

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralCompactSupportCohomologyClass_pullback_enlargement
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    {A B : Compacts X} (hAB : A ≤ B) (q : Nat)
    (a : integralSupportCohomology (A : Set X) q) :
    integralCompactSupportCohomologyClass B q
      ((integralSupportOpenEmbeddingCohomologyIso f hf B q).hom
        (integralSupportCohomologyPushforward (image_mono hAB) q
          ((integralSupportOpenEmbeddingCohomologyIso f hf A q).inv a))) =
      integralCompactSupportCohomologyClass A q a := by
  let e := integralSupportOpenEmbeddingCohomologyIso f hf A q
  have he : e.hom (e.inv a) = a := by
    change (e.inv ≫ e.hom) a = a
    rw [e.inv_hom_id]
    rfl
  have hn := congrArg (fun k => k (e.inv a))
    (integralSupportOpenEmbeddingCohomologyIso_naturality f hf hAB q)
  apply (integralCompactSupportCohomologyClass_eq_iff _ _).mpr
  refine ⟨B, le_refl B, hAB, ?_⟩
  rw [integralSupportCohomologyPushforward_refl]
  change (integralSupportOpenEmbeddingCohomologyIso f hf B q).hom
      (integralSupportCohomologyPushforward (image_mono hAB) q (e.inv a)) = _
  change (integralSupportOpenEmbeddingCohomologyIso f hf B q).hom
      (integralSupportCohomologyPushforward (image_mono hAB) q (e.inv a)) =
        integralSupportCohomologyPushforward hAB q (e.hom (e.inv a)) at hn
  rwa [he] at hn

private theorem moduleBiprod_element_ext {A B : ModuleCat.{u} Int}
    (x y : (A ⊞ B : ModuleCat.{u} Int))
    (hfst : (biprod.fst : A ⊞ B ⟶ A).hom x = (biprod.fst : A ⊞ B ⟶ A).hom y)
    (hsnd : (biprod.snd : A ⊞ B ⟶ B).hom x = (biprod.snd : A ⊞ B ⟶ B).hom y) : x = y := by
  have h (z : (A ⊞ B : ModuleCat.{u} Int)) :
      (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
        (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom z) = z :=
    congrArg (fun k => k.hom z) (biprod.total (X := A) (Y := B))
  calc
    x = _ := (h x).symm
    _ = _ := by rw [hfst, hsnd]
    _ = y := h y

def integralCompactSupportOpenMayerVietoris
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X] : ShortComplex (ModuleCat.{u} Int) :=
  ShortComplex.mk (integralCompactSupportOpenDifference U V hU hV q)
    (integralCompactSupportOpenSum U V hU hV q)
    (integralCompactSupportOpenDifference_sum U V hU hV q)

theorem integralCompactSupportOpenMayerVietoris_exact_middle
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X] :
    (integralCompactSupportOpenMayerVietoris U V hU hV q).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro y hy
  obtain ⟨A, a, B, b, ha, hb, hsum⟩ :=
    exists_integralCompactSupportOpen_kernel_representatives U V hU hV q y hy
  change (integralCompactSupportCohomologyClass A q ≫
    integralCompactSupportCohomologyOpenMap _ _ q).hom a +
    (integralCompactSupportCohomologyClass B q ≫
      integralCompactSupportCohomologyOpenMap _ _ q).hom b = 0 at hsum
  rw [integralCompactSupportCohomologyOpenMap_class,
    integralCompactSupportCohomologyOpenMap_class] at hsum
  obtain ⟨A', B', hA, hB, hzero⟩ :=
    exists_integralCompactSupportOpen_fixed_sum_zero U V hU hV q A a B b hsum
  let fU := integralOpenSubtypeUnionInclusion U V hU
  let fV := integralOpenSubtypeUnionInclusionRight U V hV
  let hfU := integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV
  let hfV := integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV
  let K := A'.map fU fU.continuous
  let L := B'.map fV fV.continuous
  let a' : integralSupportCohomology (K : Set ↥(U ∪ V)) q :=
    integralSupportCohomologyPushforward (image_mono hA) q
      ((integralSupportOpenEmbeddingCohomologyIso fU hfU A q).inv a)
  let b' : integralSupportCohomology (L : Set ↥(U ∪ V)) q :=
    integralSupportCohomologyPushforward (image_mono hB) q
      ((integralSupportOpenEmbeddingCohomologyIso fV hfV B q).inv b)
  obtain ⟨c, hca, hcb⟩ := exists_integralSupportCohomology_pair_lift
    (K : Set ↥(U ∪ V)) (L : Set ↥(U ∪ V))
    K.isCompact.isClosed L.isCompact.isClosed q a' b' hzero
  let R : Compacts ↥(U ∪ V) := ⟨(K : Set _) ∩ L, K.isCompact.inter L.isCompact⟩
  obtain ⟨z, hzU, hzV⟩ := integralCompactSupportOpenMayerVietoris_tail
    U V hU hV q A' B' R inter_subset_left inter_subset_right c
  have hclassA := integralCompactSupportCohomologyClass_pullback_enlargement fU hfU hA q a
  have hclassB := integralCompactSupportCohomologyClass_pullback_enlargement fV hfV hB q b
  have hUa := congrArg (fun t : integralSupportCohomology (K : Set ↥(U ∪ V)) q =>
    integralCompactSupportCohomologyClass A' q
      ((integralSupportOpenEmbeddingCohomologyIso fU hfU A' q).hom t)) hca
  have hVb := congrArg (fun t : integralSupportCohomology (L : Set ↥(U ∪ V)) q =>
    integralCompactSupportCohomologyClass B' q
      ((integralSupportOpenEmbeddingCohomologyIso fV hfV B' q).hom t)) hcb
  have hneg : integralCompactSupportCohomologyClass B' q
      ((integralSupportOpenEmbeddingCohomologyIso fV hfV B' q).hom (-b')) =
        -(integralCompactSupportCohomologyClass B q b) := by
    have h1 := (integralSupportOpenEmbeddingCohomologyIso fV hfV B' q).hom.hom.map_neg b'
    have h2 := (integralCompactSupportCohomologyClass B' q).hom.map_neg
      ((integralSupportOpenEmbeddingCohomologyIso fV hfV B' q).hom b')
    exact (congrArg (integralCompactSupportCohomologyClass B' q) h1).trans
      (h2.trans (congrArg Neg.neg hclassB))
  have hzU' := hzU.trans (hUa.trans (hclassA.trans ha))
  have hzV' := hzV.trans (hVb.trans (hneg.trans (congrArg Neg.neg hb)))
  refine ⟨z, moduleBiprod_element_ext _ y ?_ ?_⟩
  · change ((integralCompactSupportOpenDifference U V hU hV q) ≫
      biprod.fst).hom z = _
    rw [integralCompactSupportOpenDifference, biprod.lift_fst]
    exact hzU'
  · change ((integralCompactSupportOpenDifference U V hU hV q) ≫
      biprod.snd).hom z = _
    rw [integralCompactSupportOpenDifference, biprod.lift_snd]
    change -(integralCompactSupportCohomologyOpenMap _ _ q).hom z = _
    have he := congrArg Neg.neg hzV'
    simpa only [neg_neg] using he

end PoincareConjecture.Proofs.M02.Topology
