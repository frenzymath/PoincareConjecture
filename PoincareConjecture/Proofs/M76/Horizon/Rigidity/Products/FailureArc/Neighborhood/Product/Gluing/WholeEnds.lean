import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Instances.Real.Lemmas



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

private theorem componentIn_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hconn : IsPreconnected A) {x : X} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = A := by
  apply subset_antisymm
  · have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (x := x) (F := A ∪ B)) A B hA hB
      (connectedComponentIn_subset _ _) (by rw [hdis.inter_eq, inter_empty])
    rcases hsplit with h | h
    · exact h
    · exact False.elim (disjoint_left.mp hdis hx
        (h (mem_connectedComponentIn (Or.inl hx))))
  · exact hconn.subset_connectedComponentIn hx subset_union_left

theorem whole_ends_of_frontier_recognition
    {X C : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace C]
    {R : Set X} (hR : IsCompact R) (hconn : IsPreconnected R)
    (H : (C × Icc (0 : ℝ) 1) ≃ₜ R)
    (hfront : ∀ x t, (H (x, t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    let A := range (fun x => (H (x, ⟨0, by norm_num⟩) : X))
    let B := range (fun x => (H (x, ⟨1, by norm_num⟩) : X))
    frontier R = A ∪ B ∧ Disjoint A B ∧
      (∀ x, connectedComponentIn (frontier R) (H (x, ⟨0, by norm_num⟩) : X) = A) ∧
      ∀ x, connectedComponentIn (frontier R) (H (x, ⟨1, by norm_num⟩) : X) = B := by
  dsimp only
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp hconn
  let endpoint (t : Icc (0 : ℝ) 1) : R → X := fun y => H ((H.symm y).1, t)
  have hc (t : Icc (0 : ℝ) 1) : Continuous (endpoint t) :=
    continuous_subtype_val.comp (H.continuous.comp
      ((continuous_fst.comp H.symm.continuous).prodMk continuous_const))
  have hrange (t : Icc (0 : ℝ) 1) : range (endpoint t) =
      range (fun x => (H (x, t) : X)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(H.symm y).1, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨H (x, t), by simp [endpoint]⟩
  have hcompact (t : Icc (0 : ℝ) 1) : IsCompact (range (fun x => (H (x, t) : X))) :=
    hrange t ▸ isCompact_range (hc t)
  have hconnected (t : Icc (0 : ℝ) 1) : IsPreconnected (range (fun x => (H (x, t) : X))) :=
    hrange t ▸ isPreconnected_range (hc t)
  have hdis : Disjoint (range (fun x => (H (x, ⟨0, by norm_num⟩) : X)))
      (range (fun x => (H (x, ⟨1, by norm_num⟩) : X))) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have ht := congrArg (fun p : C × Icc (0 : ℝ) 1 => (p.2 : ℝ))
      (H.injective (Subtype.ext hy))
    norm_num at ht
  have hboundary : frontier R =
      range (fun x => (H (x, ⟨0, by norm_num⟩) : X)) ∪
      range (fun x => (H (x, ⟨1, by norm_num⟩) : X)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, t⟩, hxt⟩ := H.surjective ⟨z, hR.isClosed.frontier_subset hz⟩
      have hval := congrArg Subtype.val hxt
      rcases (hfront x t).mp (hval.symm ▸ hz) with ht | ht
      · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
        exact Or.inl ⟨x, ht' ▸ hval⟩
      · have ht' : t = ⟨1, by norm_num⟩ := Subtype.ext ht
        exact Or.inr ⟨x, ht' ▸ hval⟩
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact (hfront x _).mpr (Or.inl rfl)
      · exact (hfront x _).mpr (Or.inr rfl)
  refine ⟨hboundary, hdis, ?_, ?_⟩
  · intro x
    rw [hboundary]
    exact componentIn_union_eq (hcompact _).isClosed (hcompact _).isClosed hdis
      (hconnected _) (mem_range_self x)
  · intro x
    rw [hboundary, union_comm]
    exact componentIn_union_eq (hcompact _).isClosed (hcompact _).isClosed hdis.symm
      (hconnected _) (mem_range_self x)



theorem exists_product_on_marked_whole_boundary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {R B F₀ F₁ : Set X} (hR : IsCompact R) (hconn : IsPreconnected R)
    (H : (B × Icc (0 : ℝ) 1) ≃ₜ R)
    (hzero : ∀ x, (H (x, ⟨0, by norm_num⟩) : X) = x)
    (hfront : ∀ x t, (H (x, t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (x₀ x₁ : B)
    (hF₀ : connectedComponentIn (frontier R) (x₀ : X) = F₀)
    (hF₁ : connectedComponentIn (frontier R) (H (x₁, ⟨1, by norm_num⟩) : X) = F₁) :
    ∃ (e : F₀ ≃ₜ B) (H' : (F₀ × Icc (0 : ℝ) 1) ≃ₜ R),
      (∀ x, (e x : X) = x) ∧
      (∀ x t, H' (x, t) = H (e x, t)) ∧
      (∀ x, (H' (x, ⟨0, by norm_num⟩) : X) = x) ∧
      range (fun x => (H' (x, ⟨1, by norm_num⟩) : X)) = F₁ := by
  obtain ⟨_, _, hbottom, htop⟩ := whole_ends_of_frontier_recognition hR hconn H hfront
  have hbase : range (fun x => (H (x, ⟨0, by norm_num⟩) : X)) = B := by
    simp only [hzero, Subtype.range_coe]
  have hB : B = F₀ := by
    have h := hbottom x₀
    rw [hzero, hbase] at h
    exact h.symm.trans hF₀
  let e : F₀ ≃ₜ B := Homeomorph.setCongr hB.symm
  let H' := (e.prodCongr (Homeomorph.refl (Icc (0 : ℝ) 1))).trans H
  refine ⟨e, H', fun _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro x
    change (H (e x, ⟨0, by norm_num⟩) : X) = x
    exact hzero (e x)
  · have ht := (htop x₁).symm.trans hF₁
    rw [← ht]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e.symm x, ?_⟩
      change (H (e (e.symm x), ⟨1, by norm_num⟩) : X) = _
      rw [e.apply_symm_apply]

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
