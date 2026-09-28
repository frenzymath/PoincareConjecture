import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcEnd
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcRadialImage








set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76

theorem complement_ball_image_eq_outside_union_shell
    {V Y : Type*} [NormedAddCommGroup V] {q : V → Y} {r : ℝ}
    (hr : 0 < r) (hi : InjOn q (closedBall (0 : V) r)) :
    (q '' ball (0 : V) (r / 2))ᶜ =
      (q '' ball (0 : V) r)ᶜ ∪ q '' {x : V | r / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ r} := by
  ext y
  constructor
  · intro hy
    by_cases hh : y ∈ q '' ball (0 : V) r
    · obtain ⟨x,hx,rfl⟩ := hh
      refine Or.inr ⟨x,⟨?_,(mem_ball_zero_iff.mp hx).le⟩,rfl⟩
      by_contra hn
      exact hy ⟨x,mem_ball_zero_iff.mpr (lt_of_not_ge hn),rfl⟩
    · exact Or.inl hh
  · rintro (hy | ⟨x,hx,rfl⟩)
    · exact fun hh => hy ((image_mono (ball_subset_ball (by linarith))) hh)
    · rintro ⟨z,hz,hzq⟩
      have heq := hi (mem_closedBall_zero_iff.mpr (by
          have hh := mem_ball_zero_iff.mp hz
          linarith)) (mem_closedBall_zero_iff.mpr hx.2) hzq
      have hh := mem_ball_zero_iff.mp hz
      rw [heq] at hh
      exact (not_lt_of_ge hx.1) hh

theorem HamiltonMarkedProtectedBall.range_closed_annular_end_embedding
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ {B : Set X} (a : sphere (0 : ι → ℝ) 1),
    let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a.val}
    ∀ (H : (sphere (0 : Fin 2 → ℝ) 1 × unitInterval) ≃ₜ B)
      (F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup))
      (v : C(sphere (0 : Fin 2 → ℝ) 1,κ → ℝ)),
      Function.Injective v → (∀ y, ‖v y‖ = (3/2 : ℝ)) →
      (∀ x : A, F ⟨x,Or.inl x.property⟩ = x.val.2) →
      (∀ z, F ⟨H z,Or.inr (H z).property⟩ =
        QuotientAddGroup.mk ((1 - (z.2 : ℝ) / 2) • v z.1)) →
      range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
        Metric.ball 0 (3/4))ᶜ := by
  intro X R E B a A H F v hvi hvn hFA hFB
  have hv := range_eq_sphere_of_injective_circle (by omega : Fintype.card κ = 2)
    (by norm_num : (0 : ℝ) < 3/2) v hvi hvn
  have hrad := range_radial_half_collar (by norm_num : (0 : ℝ) < 3/2) v hv
  have hqi := b.quotient_injOn_attaching_disk (by omega)
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    rcases x.property with hx | hx
    · have hval := hFA ⟨x,hx⟩
      change F x = x.val.2 at hval
      rw [hval]
      exact fun hh => b.old_exterior_boundary_outside_open_patch he hdim hi hx.1
        ((image_mono (Metric.ball_subset_ball (by norm_num : (3/4 : ℝ) ≤ 3/2))) hh)
    · let z := H.symm ⟨x,hx⟩
      have hval : F x = QuotientAddGroup.mk ((1 - (z.2 : ℝ) / 2) • v z.1) := by
        have hh := hFB z
        simpa [z] using hh
      rw [hval]
      have hz := hrad.subset (mem_range_self z)
      rintro ⟨w,hw,hwq⟩
      have hsame := hqi (mem_closedBall_zero_iff.mpr (by
        have hh := mem_ball_zero_iff.mp hw; linarith)) (mem_closedBall_zero_iff.mpr hz.2) hwq
      have hh := mem_ball_zero_iff.mp hw
      rw [hsame] at hh
      norm_num at hz
      linarith [hz.1]
  · intro hy
    by_cases hbig : y ∈ (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
        Metric.ball 0 (3/2)
    · obtain ⟨w,hw,rfl⟩ := hbig
      have hwlow : (3/4 : ℝ) ≤ ‖w‖ := by
        by_contra hn
        exact hy ⟨w,mem_ball_zero_iff.mpr (lt_of_not_ge hn),rfl⟩
      obtain ⟨z,hz⟩ := hrad.symm.subset
        (show (3/2 : ℝ) / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 3/2 by
          constructor <;> linarith [mem_ball_zero_iff.mp hw])
      exact ⟨⟨H z,Or.inr (H z).property⟩,(hFB z).trans (congrArg QuotientAddGroup.mk hz)⟩
    · have hf : (a.val,y) ∈ frontier R := by
        change (a.val,y) ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
          (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup)))
        rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero]
        exact ⟨a.property,mem_univ _⟩
      have hE := b.old_boundary_outside_open_patch_mem_exterior he hdim hi hf hbig
      let x : A := ⟨(a.val,y),⟨⟨hE,hf⟩,rfl⟩⟩
      exact ⟨⟨x,Or.inl x.property⟩,hFA x⟩

theorem HamiltonMarkedProtectedBall.exists_closed_annular_end_quotient_embedding_with_image
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ {B : Set X}, IsClosed B → B ⊆ E ∩ D →
    ∀ H : ((sphere (0 : Fin 2 → ℝ) 1) × unitInterval) ≃ₜ B,
    (∀ z, (H z : X) ∈ frontier R ↔ (z.2 : ℝ) = 0) →
    ∃ a : sphere (0 : ι → ℝ) 1,
      let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a.val}
      ∃ F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
        (∀ x : A, F ⟨x,Or.inl x.property⟩ = x.val.2) ∧
        (∀ z, F ⟨H z,Or.inr (H z).property⟩ ∈
          (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
            Metric.ball 0 (3/2) ↔ (z.2 : ℝ) ≠ 0) ∧
        F.Homotopic ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩ ∧
        (∀ y, (H (y,0) : X).1 = a.val) ∧
        ∃ v : C((sphere (0 : Fin 2 → ℝ) 1),κ → ℝ), Function.Injective v ∧ (∀ y, ‖v y‖ = (3/2 : ℝ)) ∧
          (∀ y, (QuotientAddGroup.mk (v y) : (κ → ℝ) ⧸ L.toAddSubgroup) =
            (H (y,0) : X).2) ∧
          (∀ z, F ⟨H z,Or.inr (H z).property⟩ =
            QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1)) ∧
          range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
            Metric.ball 0 (3/4))ᶜ := by
  intro X R E B hB hBE H hHr
  let CY := sphere (0 : Fin 2 → ℝ) 1
  let : ConnectedSpace CY := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank];simp) (0 : Fin 2 → ℝ) zero_le_one)
  let : Nonempty CY := (NormedSpace.sphere_nonempty.mpr zero_le_one :
    (sphere (0 : Fin 2 → ℝ) 1).Nonempty).to_subtype
  obtain ⟨a,F,hFi,hFA,hFball,hFhom,ha,v,hvi,hvn,hv,hFB⟩ :=
    b.exists_closed_annular_end_quotient_embedding_with_lift he hdim hi hB hBE H hHr
  exact ⟨a,F,hFi,hFA,hFball,hFhom,ha,v,hvi,hvn,hv,hFB,
    b.range_closed_annular_end_embedding he hdim hi a H F v hvi hvn hFA hFB⟩

end PoincareConjecture.M76
