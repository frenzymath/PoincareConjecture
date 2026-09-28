import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportRangeMap
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCohomologyNaturality
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSubtype









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

def integralOpenIntersectionUnionInclusion
    (U V : Set X) (hU : IsOpen U) : C(↥(U ∩ V), ↥(U ∪ V)) :=
  (integralOpenSubtypeUnionInclusion U V hU).comp
    (integralOpenSubtypeInclusion U V hU)

omit [T2Space X] in
theorem integralOpenIntersectionUnionInclusion_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    _root_.Topology.IsOpenEmbedding (integralOpenIntersectionUnionInclusion U V hU) :=
  (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV).comp
    (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)

def integralCompactSupportOpenPairUnion
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) : Compacts ↥(U ∪ V) :=
  A.map (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion U V hU).continuous ⊔
    B.map (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight U V hV).continuous

def integralCompactSupportOpenPairIntersection
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) : Compacts ↥(U ∪ V) :=
  A.map (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion U V hU).continuous ⊓
    B.map (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight U V hV).continuous

omit [T2Space X] in
theorem integralCompactSupportOpenPairUnion_mono
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    {A A' : Compacts U} {B B' : Compacts V} (hA : A ≤ A') (hB : B ≤ B') :
    integralCompactSupportOpenPairUnion U V hU hV A B ≤
      integralCompactSupportOpenPairUnion U V hU hV A' B' :=
  union_subset_union (image_mono hA) (image_mono hB)

theorem integralCompactSupportOpenPairIntersection_mono
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    {A A' : Compacts U} {B B' : Compacts V} (hA : A ≤ A') (hB : B ≤ B') :
    integralCompactSupportOpenPairIntersection U V hU hV A B ≤
      integralCompactSupportOpenPairIntersection U V hU hV A' B' :=
  inter_subset_inter (image_mono hA) (image_mono hB)

theorem integralCompactSupportOpenPairIntersection_subset_range
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) :
    (integralCompactSupportOpenPairIntersection U V hU hV A B : Set ↥(U ∪ V)) ⊆
      Set.range (integralOpenIntersectionUnionInclusion U V hU) := by
  intro x hx
  rcases hx with ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
  have hxa : (x : X) ∈ U := by
    rw [← ha]
    exact a.property
  have hxb : (x : X) ∈ V := by
    rw [← hb]
    exact b.property
  exact ⟨⟨x, hxa, hxb⟩, Subtype.ext rfl⟩

def integralCompactSupportOpenConnectingStage
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat) :
    integralSupportCohomology
        (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V)) q ⟶
      integralCompactSupportCohomology ↥(U ∩ V) (q + 1) :=
  integralSupportCohomologyConnecting
      (A.map (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V))
      (B.map (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V))
      (Compacts.isCompact _).isClosed (Compacts.isCompact _).isClosed q ≫
    integralCompactSupportCohomologyRangeMap
      (integralOpenIntersectionUnionInclusion U V hU)
      (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
      (integralCompactSupportOpenPairIntersection U V hU hV A B)
      (integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B) (q + 1)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem integralCompactSupportOpenConnectingStage_naturality
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    {A A' : Compacts U} {B B' : Compacts V} (hA : A ≤ A') (hB : B ≤ B')
    (q : Nat) :
    integralSupportCohomologyPushforward
        (integralCompactSupportOpenPairUnion_mono U V hU hV hA hB) q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A' B' q =
      integralCompactSupportOpenConnectingStage U V hU hV A B q := by
  have hK :
      (A.map (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V)) ⊆
      (A'.map (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V)) :=
    image_mono hA
  have hL :
      (B.map (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V)) ⊆
      (B'.map (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V)) :=
    image_mono hB
  have hn := integralSupportCohomologyConnecting_naturality hK hL
    (Compacts.isCompact _).isClosed (Compacts.isCompact _).isClosed
    (Compacts.isCompact _).isClosed (Compacts.isCompact _).isClosed q
  unfold integralCompactSupportOpenConnectingStage
  rw [← Category.assoc, ← hn, Category.assoc,
    integralCompactSupportCohomologyRangeMap_naturality _ _
      (integralCompactSupportOpenPairIntersection_mono U V hU hV hA hB)]

theorem integralCompactSupportOpenConnectingStage_independent
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (P : Compacts ↥(U ∪ V)) (A A' : Compacts U) (B B' : Compacts V)
    (hP : P ≤ integralCompactSupportOpenPairUnion U V hU hV A B)
    (hP' : P ≤ integralCompactSupportOpenPairUnion U V hU hV A' B') (q : Nat) :
    integralSupportCohomologyPushforward hP q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A B q =
      integralSupportCohomologyPushforward hP' q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A' B' q := by
  have hAB := integralCompactSupportOpenPairUnion_mono U V hU hV
    (show A ≤ A ⊔ A' from le_sup_left) (show B ≤ B ⊔ B' from le_sup_left)
  have hAB' := integralCompactSupportOpenPairUnion_mono U V hU hV
    (show A' ≤ A ⊔ A' from le_sup_right) (show B' ≤ B ⊔ B' from le_sup_right)
  rw [← integralCompactSupportOpenConnectingStage_naturality U V hU hV
      (show A ≤ A ⊔ A' from le_sup_left) (show B ≤ B ⊔ B' from le_sup_left) q,
    ← integralCompactSupportOpenConnectingStage_naturality U V hU hV
      (show A' ≤ A ⊔ A' from le_sup_right) (show B' ≤ B ⊔ B' from le_sup_right) q,
    ← Category.assoc, integralSupportCohomologyPushforward_comp hP hAB q,
    ← Category.assoc, integralSupportCohomologyPushforward_comp hP' hAB' q]

theorem exists_integralCompactSupportOpen_cover
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (P : Compacts ↥(U ∪ V)) :
    ∃ AB : Compacts U × Compacts V,
      P ≤ integralCompactSupportOpenPairUnion U V hU hV AB.1 AB.2 := by
  obtain ⟨A, B, _, _, hAB⟩ := exists_integralCompact_union_refinement U V hU hV
    ⊥ ⊥ P (by rintro _ ⟨x, hx, _⟩; exact hx.elim)
      (by rintro _ ⟨x, hx, _⟩; exact hx.elim)
  exact ⟨(A, B), hAB.symm.le⟩

def integralCompactSupportOpenCover
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (P : Compacts ↥(U ∪ V)) :
    Compacts U × Compacts V :=
  Classical.choose (exists_integralCompactSupportOpen_cover U V hU hV P)

theorem integralCompactSupportOpenCover_spec
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (P : Compacts ↥(U ∪ V)) :
    P ≤ integralCompactSupportOpenPairUnion U V hU hV
      (integralCompactSupportOpenCover U V hU hV P).1
      (integralCompactSupportOpenCover U V hU hV P).2 :=
  Classical.choose_spec (exists_integralCompactSupportOpen_cover U V hU hV P)

def integralCompactSupportOpenConnectingComponent
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (P : Compacts ↥(U ∪ V)) :
    integralSupportCohomology (P : Set ↥(U ∪ V)) q ⟶
      integralCompactSupportCohomology ↥(U ∩ V) (q + 1) :=
  integralSupportCohomologyPushforward
      (integralCompactSupportOpenCover_spec U V hU hV P) q ≫
    integralCompactSupportOpenConnectingStage U V hU hV
      (integralCompactSupportOpenCover U V hU hV P).1
      (integralCompactSupportOpenCover U V hU hV P).2 q

theorem integralCompactSupportOpenConnectingComponent_eq
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (P : Compacts ↥(U ∪ V)) (A : Compacts U) (B : Compacts V)
    (hP : P ≤ integralCompactSupportOpenPairUnion U V hU hV A B) :
    integralCompactSupportOpenConnectingComponent U V hU hV q P =
      integralSupportCohomologyPushforward hP q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A B q :=
  integralCompactSupportOpenConnectingStage_independent U V hU hV P _ A _ B _ hP q

theorem integralCompactSupportOpenConnectingComponent_naturality
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (P Q : Compacts ↥(U ∪ V)) (hPQ : P ≤ Q) :
    integralSupportCohomologyPushforward hPQ q ≫
        integralCompactSupportOpenConnectingComponent U V hU hV q Q =
      integralCompactSupportOpenConnectingComponent U V hU hV q P := by
  let AB := integralCompactSupportOpenCover U V hU hV Q
  have hQ : Q ≤ integralCompactSupportOpenPairUnion U V hU hV AB.1 AB.2 :=
    integralCompactSupportOpenCover_spec U V hU hV Q
  rw [integralCompactSupportOpenConnectingComponent_eq U V hU hV q Q AB.1 AB.2 hQ,
    integralCompactSupportOpenConnectingComponent_eq U V hU hV q P AB.1 AB.2
      (hPQ.trans hQ), ← Category.assoc, integralSupportCohomologyPushforward_comp hPQ hQ q]

def integralCompactSupportOpenConnecting
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    integralCompactSupportCohomology ↥(U ∪ V) q ⟶
      integralCompactSupportCohomology ↥(U ∩ V) (q + 1) :=
  integralCompactSupportCohomologyDesc q _
    (integralCompactSupportOpenConnectingComponent U V hU hV q)
    (integralCompactSupportOpenConnectingComponent_naturality U V hU hV q)

@[reassoc]
theorem integralCompactSupportOpenConnecting_class
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (P : Compacts ↥(U ∪ V)) (A : Compacts U) (B : Compacts V)
    (hP : P ≤ integralCompactSupportOpenPairUnion U V hU hV A B) :
    integralCompactSupportCohomologyClass P q ≫
        integralCompactSupportOpenConnecting U V hU hV q =
      integralSupportCohomologyPushforward hP q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A B q := by
  rw [integralCompactSupportOpenConnecting, integralCompactSupportCohomologyClass_desc]
  exact integralCompactSupportOpenConnectingComponent_eq U V hU hV q P A B hP

@[reassoc]
theorem integralCompactSupportOpenConnecting_pair_class
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (A : Compacts U) (B : Compacts V) :
    integralCompactSupportCohomologyClass
        (integralCompactSupportOpenPairUnion U V hU hV A B) q ≫
        integralCompactSupportOpenConnecting U V hU hV q =
      integralCompactSupportOpenConnectingStage U V hU hV A B q := by
  rw [integralCompactSupportOpenConnecting_class U V hU hV q _ A B le_rfl,
    integralSupportCohomologyPushforward_refl, Category.id_comp]

end PoincareConjecture.Proofs.M02.Topology
