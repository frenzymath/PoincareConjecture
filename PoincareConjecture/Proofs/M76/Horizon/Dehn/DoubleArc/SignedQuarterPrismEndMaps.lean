import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismFaceMaps








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_sector_end_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (eps delta : Bool) (α β : ℝ) (hαβ : α < β) {Q0 Q1 : Set E}
    (e0 : signedTubeQuarter eps delta ≃ₜ Q0) (e1 : signedTubeQuarter eps delta ≃ₜ Q1)
    (he0 : e0.IsFinitePL) (he1 : e1.IsFinitePL) (hdisj : Disjoint Q0 Q1) :
    ∃ e : ↥(signedTubeQuarter eps delta ×ˢ ({α, β} : Set ℝ)) ≃ₜ ↥(Q0 ∪ Q1),
      e.IsFinitePL ∧
      (∀ x : signedTubeQuarter eps delta,
        (e ⟨(x, α), x.property, Or.inl rfl⟩ : E) = e0 x) ∧
      ∀ x : signedTubeQuarter eps delta,
        (e ⟨(x, β), x.property, Or.inr rfl⟩ : E) = e1 x := by
  let f0 := (signedTubeQuarterEndProjection eps delta α).trans e0
  let f1 := (signedTubeQuarterEndProjection eps delta β).trans e1
  have hf0 : f0.IsFinitePL := (signedTubeQuarterEndProjection_isFinitePL eps delta α).trans he0
  have hf1 : f1.IsFinitePL := (signedTubeQuarterEndProjection_isFinitePL eps delta β).trans he1
  have hoverlap (x : ↥(signedTubeQuarter eps delta ×ˢ {α})) :
      (x : P2 × ℝ) ∈ signedTubeQuarter eps delta ×ˢ {β} ↔ (f0 x : E) ∈ Q1 := by
    constructor
    · intro hx
      exact (hαβ.ne (x.property.2.symm.trans hx.2)).elim
    · intro hx
      exact (disjoint_left.mp hdisj (f0 x).property hx).elim
  have hagree (x : P2 × ℝ) (h0 : x ∈ signedTubeQuarter eps delta ×ˢ {α})
      (h1 : x ∈ signedTubeQuarter eps delta ×ˢ {β}) :
      (f0 ⟨x, h0⟩ : E) = f1 ⟨x, h1⟩ :=
    (hαβ.ne (h0.2.symm.trans h1.2)).elim
  obtain ⟨f, hf, hkeep0, hkeep1⟩ :=
    Homeomorph.exists_union_finitePL f0 f1 hf0 hf1 hoverlap hagree
  have hsource : (signedTubeQuarter eps delta ×ˢ {α}) ∪
      (signedTubeQuarter eps delta ×ˢ {β}) =
        signedTubeQuarter eps delta ×ˢ ({α, β} : Set ℝ) := by
    ext x
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  let e := (Homeomorph.setCongr hsource.symm).trans f
  refine ⟨e, hf.setCongr hsource rfl, ?_, ?_⟩
  · intro x
    exact hkeep0 ⟨(x, α), x.property, rfl⟩
  · intro x
    exact hkeep1 ⟨(x, β), x.property, rfl⟩

theorem signed_half_face_end_preimage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (eps delta : Bool) (i : Fin 2) (sign : Bool) (α β t : ℝ) (ht : t ∈ Icc α β)
    {F Q : Set E} (hRQ : signedTubeRadius i sign ⊆ signedTubeQuarter eps delta)
    (f : ↥(signedTubeRadius i sign ×ˢ Icc α β) ≃ₜ F)
    (e : signedTubeQuarter eps delta ≃ₜ Q)
    (hcontact : ∀ x : signedTubeQuarter eps delta,
      (e x : E) ∈ F ↔ (x : P2) ∈ signedTubeRadius i sign)
    (hkeep : ∀ x : signedTubeRadius i sign,
      (f ⟨(x, t), x.property, ht⟩ : E) = e ⟨x, hRQ x.property⟩)
    (x : ↥(signedTubeRadius i sign ×ˢ Icc α β)) :
    (x : P2 × ℝ).2 = t ↔ (f x : E) ∈ Q := by
  constructor
  · intro htime
    have heq : x = ⟨((x : P2 × ℝ).1, t), x.property.1, ht⟩ :=
      Subtype.ext (Prod.ext rfl htime)
    rw [heq]
    exact (hkeep ⟨(x : P2 × ℝ).1, x.property.1⟩).symm ▸ (e _).property
  · intro hQ
    let y := e.symm ⟨f x, hQ⟩
    have hyval : (e y : E) = f x := congrArg Subtype.val (e.apply_symm_apply _)
    have hyR : (y : P2) ∈ signedTubeRadius i sign :=
      (hcontact y).mp (hyval.symm ▸ (f x).property)
    have hfy : f ⟨(y, t), hyR, ht⟩ = f x :=
      Subtype.ext ((hkeep ⟨y, hyR⟩).trans hyval)
    exact (congrArg (fun z : ↥(signedTubeRadius i sign ×ˢ Icc α β) =>
      (z : P2 × ℝ).2) (f.injective hfy)).symm

end PoincareConjecture.M76.Dehn
