import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapOpenAmbient
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapBoundaryCompatibility
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOriginalAtlasGluing
import PoincareConjecture.Proofs.M76.Mathlib.AffineChartInclusion











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "M" => (ℝ × (Fin 2 → ℝ))

variable {X : Type*} [TopologicalSpace X] {Y : Set X} {ι : Type*}






theorem PLDomain.marked_cap_charts_compatible
    {e : ι → OpenPartialHomeomorph Y V3} {K : Set Y} (hKD : PLDomain e K)
    {D S : Set X} {eps : ℝ} {U : Set D} (g : (S × Ico (0 : ℝ) eps) ≃ₜ U)
    (c d : HamiltonMarkedCapCoordinates (E := Fin 2 → ℝ) (D := D)
      (fun p => ((g p : D) : X)))
    (B0 B1 : OpenPartialHomeomorph Y V3)
    (hB0 : ∀ i, (e i).symm.trans B0 ∈ piecewiseAffineGroupoid V3)
    (hB1 : ∀ i, (e i).symm.trans B1 ∈ piecewiseAffineGroupoid V3)
    (a b : V3 ≃ᴬ[ℝ] M) {Nc Nd : Set Y}
    (hcinv : ∀ z ∈ c.original.target, a.symm z ∈ B0.target ∧
      B0.symm (a.symm z) ∈ Nc ∧ c.original.symm z = (B0.symm (a.symm z) : X))
    (hds : d.original.source = (Subtype.val : Y → X) '' (B1.source ∩ Nd))
    (hdval : ∀ z : Y, z ∈ B1.source ∩ Nd → d.original z = b (B1 z))
    (q : M ≃ᴬ[ℝ] V3) :
    (c.chart.transHomeomorph q.toHomeomorph).symm.trans
      (d.chart.transHomeomorph q.toHomeomorph) ∈ piecewiseAffineGroupoid V3 := by
  have hBB : B0.symm.trans B1 ∈ piecewiseAffineGroupoid V3 :=
    pl_transition_mem_of_overlap_cover e B0 B1 (fun x _ => hKD.cover x) hB0 hB1
  have hold : c.original.symm.trans d.original ∈ piecewiseAffineGroupoid M := by
    apply OpenPartialHomeomorph.affine_inclusion_transition_mem_piecewiseAffineGroupoid
      (Subtype.val : Y → X) Subtype.val_injective B0 B1 hBB a b c.original d.original
    · intro z hz
      exact ⟨(hcinv z hz).1, (hcinv z hz).2.2⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hds.subset hx
      exact ⟨y, hy.1, rfl, hdval y hy⟩
  have hnew : c.chart.symm.trans d.chart ∈ piecewiseAffineGroupoid M := by
    apply c.compatible d (fun p => (g p : D).property) ?_ hold
    intro p r hpr
    apply g.injective
    apply Subtype.ext
    exact Subtype.ext hpr
  apply OpenPartialHomeomorph.affine_inclusion_transition_mem_piecewiseAffineGroupoid
    (fun x : X => x) Function.injective_id c.chart d.chart hnew q q
    (c.chart.transHomeomorph q.toHomeomorph) (d.chart.transHomeomorph q.toHomeomorph)
  · intro z hz
    exact ⟨hz, rfl⟩
  · intro x hx
    exact ⟨x, hx, rfl, rfl⟩

end PoincareConjecture.M76
