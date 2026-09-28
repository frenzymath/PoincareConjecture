import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedSidePasting
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter PoincareConjecture
open scoped Manifold ContDiff Topology

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

private theorem ambient_cylinder_chart (A : Opens M)
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A ∞) :
    ∃ a : OpenPartialHomeomorph RoundCylinderSpace M,
      a.source = univ ∧ a.target = (A : Set M) ∧
      ContMDiffOn CylModel (𝓡 3) ∞ a a.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ a.symm a.target ∧
      ∀ p : RoundCylinderSpace, a p = (F p : M) := by
  let : Nonempty UnitTwoSphere :=
    (NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).coe_sort
  let : Nonempty A := F.toEquiv.symm.nonempty
  let i : OpenPartialHomeomorph A M := A.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ i.symm i.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff A i.symm i.target x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact i.right_inv hy
    · exact i.right_inv hx
  let a := F.toHomeomorph.toOpenPartialHomeomorph.trans i
  have has : a.source = univ := by simp [a, i]
  have hat : a.target = (A : Set M) := by simp [a, i]
  refine ⟨a, has, hat, ?_, ?_, fun _ => rfl⟩
  · exact contMDiff_subtype_val.comp_contMDiffOn
      (F.contMDiff.contMDiffOn.mono inter_subset_left)
  · exact F.symm.contMDiff.comp_contMDiffOn (hi.mono inter_subset_left)

theorem exists_absorption_of_matching_cylinders
    (U A B : Opens M) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U)
    (hAU : (A : Set M) ⊆ U) (hAB : (A : Set M) ⊆ B)
    (houtside : (U : Set M) \ K ⊆ A)
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A ∞)
    (G : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B ∞)
    (hFside : ∀ p : RoundCylinderSpace, (F p : M) ∈ K ↔ p.2 ≤ 0)
    (hGside : ∀ p : RoundCylinderSpace, (G p : M) ∈ K ↔ p.2 ≤ 0)
    (hfront : frontier K = range (fun q : UnitTwoSphere => (F (q, 0) : M)))
    {r : ℝ} (hr : 0 < r)
    (hagree : ∀ p : RoundCylinderSpace, |p.2| < r → (F p : M) = G p) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) U (↥(U ⊔ B)) ∞,
      (∀ x : U, (x : M) ∈ K → (D x : M) = x) ∧
      ∀ p : RoundCylinderSpace, 0 < p.2 →
        ∀ x : U, (x : M) = F p → (D x : M) = G p := by
  obtain ⟨a, has, hat, ha, hai, hav⟩ := ambient_cylinder_chart A F
  obtain ⟨b, hbs, hbt, hb, hbi, hbv⟩ := ambient_cylinder_chart B G
  let e := a.symm.trans' b (has.trans hbs.symm)
  have hes : e.source = (A : Set M) := hat
  have het : e.target = (B : Set M) := hbt
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source :=
    hb.comp hai (fun x hx => hbs.symm ▸ mem_univ _)
  have hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target :=
    ha.comp hbi (fun x hx => has.symm ▸ mem_univ _)
  have heap (p : RoundCylinderSpace) : e (a p) = b p := by
    change b (a.symm (a p)) = b p
    rw [a.left_inv (has.symm ▸ mem_univ p)]
  have hside (x : M) (hx : x ∈ e.source) : e x ∈ K ↔ x ∈ K := by
    have hax : a (a.symm x) = x := a.right_inv hx
    rw [← hax, heap, hav, hbv, hFside, hGside]
  let N := a '' {p : RoundCylinderSpace | |p.2| < r}
  have hN : IsOpen N := a.isOpen_image_of_subset_source
    (isOpen_lt continuous_snd.abs continuous_const) (by rw [has]; exact subset_univ _)
  have hNs : N ⊆ e.source := by
    rintro x ⟨p, _, rfl⟩
    exact a.map_source (has.symm ▸ mem_univ p)
  have heN : EqOn e id N := by
    rintro x ⟨p, hp, rfl⟩
    rw [heap, hbv, hav]
    exact (hagree p hp).symm
  have hiN : EqOn e.symm id N := by
    intro x hx
    have h := e.left_inv (hNs hx)
    rwa [heN hx] at h
  have hfN : frontier K ⊆ N := by
    rw [hfront]
    rintro x ⟨q, rfl⟩
    exact ⟨(q, 0), by simpa using hr, hav _⟩
  obtain ⟨D, hD, _, hDK⟩ := exists_diffeomorph_of_closed_side_replacement
    U (U ⊔ B) hK hKU (fun x hx => Or.inl (hKU hx)) e
    (fun x hx => hes.symm ▸ houtside hx)
    (by
      rintro x ⟨hxU | hxB, hxK⟩
      · exact het.symm ▸ hAB (houtside ⟨hxU, hxK⟩)
      · exact het.symm ▸ hxB)
    (hes ▸ hAU) (fun x hx => Or.inr (het ▸ hx)) he hei hside
    (fun x hx => Filter.eventuallyEq_of_mem (hN.mem_nhds (hfN hx)) heN)
    (fun x hx => Filter.eventuallyEq_of_mem (hN.mem_nhds (hfN hx)) hiN)
  refine ⟨D, hDK, ?_⟩
  intro p hp x hx
  have hxK : (x : M) ∉ K := fun h => (not_le_of_gt hp) ((hFside p).mp (hx ▸ h))
  rw [hD x, if_neg hxK, hx, ← hav, heap, hbv]

end Poincare
