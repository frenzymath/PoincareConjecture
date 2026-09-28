import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSubtype










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_integralCompactSupportOpen_kernel_representatives
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X]
    (y : (integralCompactSupportCohomology U q ⊞
      integralCompactSupportCohomology V q : ModuleCat.{u} Int))
    (hy : (integralCompactSupportOpenSum U V hU hV q).hom y = 0) :
    ∃ (A : Compacts U) (aA : integralSupportCohomology (A : Set U) q)
      (B : Compacts V) (bB : integralSupportCohomology (B : Set V) q),
      (integralCompactSupportCohomologyClass A q).hom aA =
          (biprod.fst : integralCompactSupportCohomology U q ⊞
            integralCompactSupportCohomology V q ⟶
              integralCompactSupportCohomology U q).hom y ∧
      (integralCompactSupportCohomologyClass B q).hom bB =
          (biprod.snd : integralCompactSupportCohomology U q ⊞
            integralCompactSupportCohomology V q ⟶
              integralCompactSupportCohomology V q).hom y ∧
      (integralCompactSupportCohomologyOpenMap
        (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) q).hom
          ((integralCompactSupportCohomologyClass A q).hom aA) +
        (integralCompactSupportCohomologyOpenMap
          (integralOpenSubtypeUnionInclusionRight U V hV)
          (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) q).hom
            ((integralCompactSupportCohomologyClass B q).hom bB) = 0 := by
  let a := (biprod.fst :
    integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q ⟶
      integralCompactSupportCohomology U q).hom y
  let b := (biprod.snd :
    integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q ⟶
      integralCompactSupportCohomology V q).hom y
  have hydecomp := congrArg (fun f => f.hom y)
    (biprod.total :
      (biprod.fst : integralCompactSupportCohomology U q ⊞
          integralCompactSupportCohomology V q ⟶ integralCompactSupportCohomology U q) ≫
          (biprod.inl : integralCompactSupportCohomology U q ⟶
            integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q) +
        (biprod.snd : integralCompactSupportCohomology U q ⊞
          integralCompactSupportCohomology V q ⟶ integralCompactSupportCohomology V q) ≫
          (biprod.inr : integralCompactSupportCohomology V q ⟶
            integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q) =
        𝟙 _)
  change
      (biprod.inl : integralCompactSupportCohomology U q ⟶
          integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q).hom a +
        (biprod.inr : integralCompactSupportCohomology V q ⟶
          integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q).hom b = y
    at hydecomp
  have hsum :
      (integralCompactSupportCohomologyOpenMap
        (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) q).hom a +
      (integralCompactSupportCohomologyOpenMap
        (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) q).hom b = 0 := by
    rw [← hydecomp] at hy
    simpa only [integralCompactSupportOpenSum, map_add,
      ← ConcreteCategory.comp_apply, biprod.inl_desc, biprod.inr_desc,
      Category.comp_id, Category.id_comp] using hy
  obtain ⟨A, aA, ha⟩ := exists_integralCompactSupportCohomology_representative q a
  obtain ⟨B, bB, hb⟩ := exists_integralCompactSupportCohomology_representative q b
  refine ⟨A, aA, B, bB, ha, hb, ?_⟩
  rw [ha, hb]
  exact hsum

theorem exists_integralCompactSupportOpen_fixed_sum_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X]
    (A : Compacts U) (aA : integralSupportCohomology (A : Set U) q)
    (B : Compacts V) (bB : integralSupportCohomology (B : Set V) q)
    (hsum :
      (integralCompactSupportCohomologyClass
        (A.map (integralOpenSubtypeUnionInclusion U V hU)
          (integralOpenSubtypeUnionInclusion U V hU).continuous) q).hom
          ((integralSupportOpenEmbeddingCohomologyIso
            (integralOpenSubtypeUnionInclusion U V hU)
            (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) A q).inv aA) +
      (integralCompactSupportCohomologyClass
        (B.map (integralOpenSubtypeUnionInclusionRight U V hV)
          (integralOpenSubtypeUnionInclusionRight U V hV).continuous) q).hom
          ((integralSupportOpenEmbeddingCohomologyIso
            (integralOpenSubtypeUnionInclusionRight U V hV)
            (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) B q).inv bB) = 0) :
    ∃ (A' : Compacts U) (B' : Compacts V) (hA : A ≤ A') (hB : B ≤ B'),
      let fU := integralOpenSubtypeUnionInclusion U V hU
      let fV := integralOpenSubtypeUnionInclusionRight U V hV
      let a₁ := (integralSupportOpenEmbeddingCohomologyIso fU
        (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) A q).inv aA
      let b₁ := (integralSupportOpenEmbeddingCohomologyIso fV
        (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) B q).inv bB
      let K : Set ↥(U ∪ V) := (A'.map fU fU.continuous : Set ↥(U ∪ V))
      let L : Set ↥(U ∪ V) := (B'.map fV fV.continuous : Set ↥(U ∪ V))
      let a' : integralSupportCohomology K q :=
        integralSupportCohomologyPushforward (image_mono hA) q a₁
      let b' : integralSupportCohomology L q :=
        integralSupportCohomologyPushforward (image_mono hB) q b₁
      integralSupportCohomologyPushforward (subset_union_left : K ⊆ K ∪ L) q a' +
        integralSupportCohomologyPushforward (subset_union_right : L ⊆ K ∪ L) q b' = 0 := by
  let fU := integralOpenSubtypeUnionInclusion U V hU
  let fV := integralOpenSubtypeUnionInclusionRight U V hV
  let hfU := integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV
  let hfV := integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV
  let A₁ := A.map fU fU.continuous
  let B₁ := B.map fV fV.continuous
  let a₁ : integralSupportCohomology (A₁ : Set ↥(U ∪ V)) q :=
    (integralSupportOpenEmbeddingCohomologyIso fU hfU A q).inv aA
  let b₁ : integralSupportCohomology (B₁ : Set ↥(U ∪ V)) q :=
    (integralSupportOpenEmbeddingCohomologyIso fV hfV B q).inv bB
  have hsumclass :
      (integralCompactSupportCohomologyClass A₁ q).hom a₁ +
        (integralCompactSupportCohomologyClass B₁ q).hom b₁ = 0 := by
    exact hsum
  let Q : Compacts ↥(U ∪ V) := A₁ ⊔ B₁
  let aQ : integralSupportCohomology (Q : Set ↥(U ∪ V)) q :=
    integralSupportCohomologyPushforward (show A₁ ≤ Q from le_sup_left) q a₁
  let bQ : integralSupportCohomology (Q : Set ↥(U ∪ V)) q :=
    integralSupportCohomologyPushforward (show B₁ ≤ Q from le_sup_right) q b₁
  let sQ := aQ + bQ
  have hsQ : (integralCompactSupportCohomologyClass Q q).hom sQ = 0 := by
    dsimp [sQ]
    rw [map_add]
    have hqa := congrArg (fun f => f.hom a₁)
      (integralCompactSupportCohomologyClass_pushforward
        (show A₁ ≤ Q from le_sup_left) q)
    have hqb := congrArg (fun f => f.hom b₁)
      (integralCompactSupportCohomologyClass_pushforward
        (show B₁ ≤ Q from le_sup_right) q)
    change (integralSupportCohomologyPushforward (show A₁ ≤ Q from le_sup_left) q ≫
      integralCompactSupportCohomologyClass Q q).hom a₁ +
      (integralSupportCohomologyPushforward (show B₁ ≤ Q from le_sup_right) q ≫
        integralCompactSupportCohomologyClass Q q).hom b₁ = 0
    rw [hqa, hqb]
    exact hsumclass
  obtain ⟨P, hQP, hzero⟩ :=
    (integralCompactSupportCohomologyClass_eq_zero_iff sQ).mp hsQ
  obtain ⟨A', B', hA, hB, hP⟩ :=
    exists_integralCompact_union_refinement U V hU hV A B P
      (show A.map fU fU.continuous ≤ P from le_sup_left.trans hQP)
      (show B.map fV fV.continuous ≤ P from le_sup_right.trans hQP)
  let K : Set ↥(U ∪ V) := (A'.map fU fU.continuous : Set ↥(U ∪ V))
  let L : Set ↥(U ∪ V) := (B'.map fV fV.continuous : Set ↥(U ∪ V))
  have hA1 : A₁ ≤ A'.map fU fU.continuous := image_mono hA
  have hB1 : B₁ ≤ B'.map fV fV.continuous := image_mono hB
  let a' : integralSupportCohomology K q :=
    integralSupportCohomologyPushforward hA1 q a₁
  let b' : integralSupportCohomology L q :=
    integralSupportCohomologyPushforward hB1 q b₁
  refine ⟨A', B', hA, hB, ?_⟩
  dsimp only
  let Q' : Compacts ↥(U ∪ V) :=
    A'.map fU fU.continuous ⊔ B'.map fV fV.continuous
  have hQ' : Q ≤ Q' := sup_le_sup hA1 hB1
  have hzero0 := hzero
  subst P
  have hzero' : integralSupportCohomologyPushforward hQ' q (aQ + bQ) = 0 := by
    simpa [Q', sQ] using hzero0
  have hzero'' :
      integralSupportCohomologyPushforward hQ' q aQ +
        integralSupportCohomologyPushforward hQ' q bQ = 0 := by
    change (integralSupportCohomologyPushforward hQ' q) (aQ + bQ) = 0 at hzero'
    rw [map_add] at hzero'
    exact hzero'
  have haQ :
      integralSupportCohomologyPushforward hQ' q aQ =
        integralSupportCohomologyPushforward
          (show A₁ ≤ Q' from hA1.trans le_sup_left) q a₁ := by
    change (integralSupportCohomologyPushforward (show A₁ ≤ Q from le_sup_left) q ≫
      integralSupportCohomologyPushforward hQ' q) a₁ = _
    rw [integralSupportCohomologyPushforward_comp]
  have hbQ :
      integralSupportCohomologyPushforward hQ' q bQ =
        integralSupportCohomologyPushforward
          (show B₁ ≤ Q' from hB1.trans le_sup_right) q b₁ := by
    change (integralSupportCohomologyPushforward (show B₁ ≤ Q from le_sup_right) q ≫
      integralSupportCohomologyPushforward hQ' q) b₁ = _
    rw [integralSupportCohomologyPushforward_comp]
  rw [haQ, hbQ] at hzero''
  change integralSupportCohomologyPushforward
      (show A'.map fU fU.continuous ≤ Q' from le_sup_left) q a' +
    integralSupportCohomologyPushforward
      (show B'.map fV fV.continuous ≤ Q' from le_sup_right) q b' = 0
  change (integralSupportCohomologyPushforward hA1 q ≫
      integralSupportCohomologyPushforward
        (show A'.map fU fU.continuous ≤ Q' from le_sup_left) q) a₁ +
    (integralSupportCohomologyPushforward hB1 q ≫
      integralSupportCohomologyPushforward
        (show B'.map fV fV.continuous ≤ Q' from le_sup_right) q) b₁ = 0
  rw [integralSupportCohomologyPushforward_comp,
    integralSupportCohomologyPushforward_comp]
  exact hzero''

end PoincareConjecture.Proofs.M02.Topology
