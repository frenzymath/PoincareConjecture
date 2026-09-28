import PoincareConjecture.Proofs.M76.Mathlib.RectangleCollarNormalization

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in

theorem rectangle_side_mem_iff
    {α β : ℝ} {T S : Set E}
    (G : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ T)
    (k : Icc (0 : ℝ) 1) (d : Icc α β ≃ₜ S)
    (hside : ∀ t : Icc α β,
      (G ⟨(k, t), ⟨k.property, t.property⟩⟩ : E) = d t)
    (p : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ))) :
    (G p : E) ∈ S ↔ (p : ℝ × ℝ).1 = k := by
  constructor
  · intro hp
    let t := d.symm ⟨G p, hp⟩
    have heq : G ⟨(k, t), ⟨k.property, t.property⟩⟩ = G p :=
      Subtype.ext ((hside t).trans (congrArg Subtype.val (d.apply_symm_apply _)))
    exact (congrArg Prod.fst (congrArg Subtype.val (G.injective heq))).symm
  · intro hp
    let t : Icc α β := ⟨(p : ℝ × ℝ).2, p.property.2⟩
    have heq : p = ⟨(k, t), ⟨k.property, t.property⟩⟩ :=
      Subtype.ext (Prod.ext hp rfl)
    rw [heq, hside]
    exact (d t).property

theorem IsFinitePL.exists_bottom_normalized_rectangle_chart_with_sides
    [FiniteDimensional ℝ E] {ι : Type*}
    {α β : ℝ} (hαβ : α < β) {T : Set E}
    {G : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ T}
    (hG : G.IsFinitePL) (A : E → ℝ)
    (hheight : ∀ p, A (G p) = (p : ℝ × ℝ).2)
    (S : ι → Set E) (k : ι → Icc (0 : ℝ) 1)
    (d : ∀ i, Icc α β ≃ₜ S i)
    (hside : ∀ i (t : Icc α β),
      (G ⟨(k i, t), ⟨(k i).property, t.property⟩⟩ : E) = d i t) :
    ∃ C : ((T ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ T,
      C.IsFinitePL ∧ (∀ p, A (C p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ T ∩ {x | A x = α}),
        (C ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x) ∧
      ∀ i (p : ((T ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ))),
        (C p : E) ∈ S i ↔ (p : E × ℝ).1 ∈ S i := by
  obtain ⟨C, hC, hCA, hbase, hformula⟩ :=
    hG.exists_bottom_normalized_rectangle_chart hαβ A hheight
  refine ⟨C, hC, hCA, hbase, ?_⟩
  intro i p
  let p₀ := G.symm ⟨(p : E × ℝ).1, p.property.1.1⟩
  have hp₀ : (G p₀ : E) = (p : E × ℝ).1 :=
    congrArg Subtype.val (G.apply_symm_apply _)
  have hp₀height : (p₀ : ℝ × ℝ).2 = α :=
    (hheight p₀).symm.trans ((congrArg A hp₀).trans p.property.1.2)
  let u : Icc (0 : ℝ) 1 := ⟨(p₀ : ℝ × ℝ).1, p₀.property.1⟩
  have heq : p₀ = ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩ :=
    Subtype.ext (Prod.ext rfl hp₀height)
  have hu : (G ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) =
      (p : E × ℝ).1 := by
    rwa [heq] at hp₀
  calc
    (C p : E) ∈ S i ↔
        (G ⟨(u, (p : E × ℝ).2), ⟨u.property, p.property.2⟩⟩ : E) ∈ S i := by
      rw [hformula p u hu]
    _ ↔ (u : ℝ) = k i := rectangle_side_mem_iff G (k i) (d i) (hside i) _
    _ ↔ (G ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) ∈ S i :=
      (rectangle_side_mem_iff G (k i) (d i) (hside i)
        ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩).symm
    _ ↔ (p : E × ℝ).1 ∈ S i := by rw [hu]

end Homeomorph
