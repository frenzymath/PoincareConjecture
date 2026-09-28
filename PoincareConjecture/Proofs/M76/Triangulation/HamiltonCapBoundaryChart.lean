import PoincareConjecture.Proofs.M76.Triangulation.HamiltonRelativeHalfChart
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedBrownCollar










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]

private def capNegativeInterval (r : ℝ) :
    Ioc (-r) (0 : ℝ) ≃ₜ Ico (0 : ℝ) r where
  toFun x := ⟨-x, by constructor <;> linarith [x.property.1, x.property.2]⟩
  invFun x := ⟨-x, by constructor <;> linarith [x.property.1, x.property.2]⟩
  left_inv x := Subtype.ext (neg_neg (x : ℝ))
  right_inv x := Subtype.ext (neg_neg (x : ℝ))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop






theorem exists_marked_cap_boundary_chart
    {K D S : Set X} (hK : IsClosed K) (hD : IsClosed D)
    (hcover : K ∪ D = univ) (hS : S = K ∩ D)
    (B : OpenPartialHomeomorph X (ℝ × E))
    (hBK : ∀ x ∈ B.source, x ∈ K ↔ 0 ≤ (B x).1)
    (hBD : ∀ x ∈ B.source, x ∈ D ↔ (B x).1 ≤ 0)
    (b : OpenPartialHomeomorph S E)
    (hbt : b.target = {z | (0, z) ∈ B.target})
    (hbi : ∀ z ∈ b.target, (b.symm z : X) = B.symm (0, z))
    {eps r : ℝ} (hr : 0 < r) (hre : r ≤ eps)
    {O : Set E} (hO : IsOpen O) (hne : O.Nonempty)
    (hrect : Set.prod (Ioo (-r) r) O ⊆ B.target)
    {U : Set D} (hU : IsOpen U) (g : (S × Ico (0 : ℝ) eps) ≃ₜ U)
    (hgzero : ∀ p : S × Ico (0 : ℝ) eps,
      (p.2 : ℝ) = 0 → ((g p : D) : X) = (p.1 : X))
    (hgS : ∀ p : S × Ico (0 : ℝ) eps,
      ((g p : D) : X) ∈ S ↔ (p.2 : ℝ) = 0) :
    let j : Set.prod (Ioc (-r) (0 : ℝ)) O → S × Ico (0 : ℝ) eps :=
      fun p => (b.symm (p : ℝ × E).2,
        ⟨-(p : ℝ × E).1, by
          constructor <;> linarith [p.property.1.1, p.property.1.2]⟩)
    ∃ H : OpenPartialHomeomorph X (ℝ × E),
      H.target = Set.prod (Ioo (-r) r) O ∧
      H.source = B.symm '' Set.prod (Ico (0 : ℝ) r) O ∪
        range (fun p => ((g (j p) : D) : X)) ∧
      (∀ p : Set.prod (Ico (0 : ℝ) r) O,
        H (B.symm (p : ℝ × E)) = (p : ℝ × E)) ∧
      ∀ p, H ((g (j p) : D) : X) = (p : ℝ × E) := by
  dsimp only
  let P := Set.prod (Ico (0 : ℝ) r) O
  let N := Set.prod (Ioc (-r) (0 : ℝ)) O
  let T := Set.prod (Ioo (-r) r) O
  let I := Ico (0 : ℝ) eps
  have hPT : P ⊆ T := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hp.2⟩
  have hPB : P ⊆ B.target := hPT.trans hrect
  have hOb : O ⊆ b.target := by
    intro z hz
    rw [hbt]
    exact hrect ⟨⟨neg_lt_zero.mpr hr, hr⟩, hz⟩
  let e : P → K := fun p => ⟨B.symm p, by
    apply (hBK _ (B.map_target (hPB p.property))).mpr
    rw [B.right_inv (hPB p.property)]
    exact p.property.1.1⟩
  have hemb : Topology.IsEmbedding (fun p : P => B.symm (p : ℝ × E)) :=
    B.symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hPB)
  have he : Topology.IsOpenEmbedding e := by
    refine ⟨hemb.codRestrict K _, ?_⟩
    have heq : range e =
        (Subtype.val : K → X) ⁻¹' (B.source ∩ B ⁻¹' T) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        refine ⟨B.map_target (hPB p.property), ?_⟩
        change B (B.symm (p : ℝ × E)) ∈ T
        rw [B.right_inv (hPB p.property)]
        exact hPT p.property
      · intro hx
        let p : P := ⟨B x, ⟨⟨(hBK x hx.1).mp x.property, hx.2.1.2⟩, hx.2.2⟩⟩
        exact ⟨p, Subtype.ext (B.left_inv hx.1)⟩
    rw [heq]
    exact (B.continuousOn_toFun.isOpen_inter_preimage B.open_source
      (isOpen_Ioo.prod hO)).preimage continuous_subtype_val
  let ib : Ico (0 : ℝ) r → I := Set.inclusion
    (fun _ ht => ⟨ht.1, ht.2.trans_le hre⟩)
  have hib : Topology.IsOpenEmbedding ib := by
    apply Topology.IsOpenEmbedding.inclusion
    have heq : (Subtype.val : I → ℝ) ⁻¹' Ico (0 : ℝ) r =
        {t : I | (t : ℝ) < r} := by
      ext t
      exact ⟨fun h => h.2, fun h => ⟨t.property.1, h⟩⟩
    rw [heq]
    exact isOpen_lt continuous_subtype_val continuous_const
  let bs : O → S := fun z => b.symm z
  have hbs : Topology.IsOpenEmbedding bs :=
    b.symm.isOpenEmbedding_restrict.comp (Topology.IsOpenEmbedding.inclusion hOb
      (hO.preimage continuous_subtype_val))
  let q : N ≃ₜ O × Ioc (-r) (0 : ℝ) :=
    (Homeomorph.Set.prod _ _).trans (Homeomorph.prodComm _ _)
  let j : N → S × I := fun p => (b.symm (p : ℝ × E).2,
    ⟨-(p : ℝ × E).1, by
      constructor <;> linarith [p.property.1.1, p.property.1.2]⟩)
  have hj : Topology.IsOpenEmbedding j :=
    (hbs.prodMap (hib.comp (capNegativeInterval r).isOpenEmbedding)).comp q.isOpenEmbedding
  let f : N → D := fun p => g (j p)
  have hf : Topology.IsOpenEmbedding f :=
    hU.isOpenEmbedding_subtypeVal.comp (g.isOpenEmbedding.comp hj)
  have heD (p : P) : (e p : X) ∈ D ↔ (p : ℝ × E).1 = 0 := by
    change B.symm (p : ℝ × E) ∈ D ↔ _
    rw [hBD _ (B.map_target (hPB p.property)), B.right_inv (hPB p.property)]
    exact ⟨fun h => le_antisymm h p.property.1.1, fun h => h.le⟩
  have hfK (p : N) : (f p : X) ∈ K ↔ (p : ℝ × E).1 = 0 := by
    have hs : (f p : X) ∈ K ↔ (f p : X) ∈ S := by
      rw [hS]
      exact ⟨fun h => ⟨h, (f p).property⟩, fun h => h.1⟩
    rw [hs, hgS (j p)]
    exact neg_eq_zero
  have hzero (p : P) (q0 : N) (hpq : (p : ℝ × E) = (q0 : ℝ × E)) :
      (e p : X) = (f q0 : X) := by
    have hq0 : (q0 : ℝ × E).1 = 0 :=
      le_antisymm q0.property.1.2 (by simpa only [hpq] using p.property.1.1)
    have hg := hgzero (j q0) (by change -(q0 : ℝ × E).1 = 0; rw [hq0, neg_zero])
    change B.symm (p : ℝ × E) = ((g (j q0) : D) : X)
    rw [hg, hbi _ (hOb q0.property.2)]
    apply congrArg B.symm
    exact hpq.trans (Prod.ext hq0 rfl)
  obtain ⟨H, hHs, hHt, hHe, hHf⟩ := exists_cap_chart_of_relative_half_embeddings
    hK hD hcover hO hne hr e he f hf heD hfK hzero
  have hrange : range (fun p : P => (e p : X)) = B.symm '' P := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  refine ⟨H, hHt, ?_, hHe, hHf⟩
  rw [hrange] at hHs
  exact hHs

end PoincareConjecture.M76
