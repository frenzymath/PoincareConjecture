import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Statements.M44Providers

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem M44CapPersistencePredecessors.scalar_continuous
    (P : M44CapPersistencePredecessors.{u}) {J : Set ℝ}
    (F : RicciFlow 3 M J) {t : ℝ} (ht : t ∈ J) :
    Continuous (F.connection t).scalarCurvature := by
  have hregular := P.curvature.scalar_regular 3 M J F
  have hslice : Continuous (fun x : M => (t, x)) :=
    continuous_const.prodMk continuous_id
  have hmem : ∀ x : M, (t, x) ∈ J ×ˢ (univ : Set M) :=
    fun x => ⟨ht, mem_univ x⟩
  have hcontinuous := hregular.continuousOn.comp_continuous hslice hmem
  exact hcontinuous

theorem SingularCComponent.scalar_le_sup {g : RiemannianMetric 3 M}
    {D : LeviCivitaData g} {C : ℝ} (N : SingularCComponent g D C)
    (hscalar : ContinuousOn D.scalarCurvature N.carrier)
    {x : M} (hx : x ∈ N.carrier) :
    D.scalarCurvature x ≤ scalarCurvatureSupOn g D N.carrier := by
  have hb : BddAbove (range (fun y : N.carrier => D.scalarCurvature y.1)) := by
    apply (N.compact.bddAbove_image hscalar).mono
    rintro _ ⟨y, rfl⟩
    exact mem_image_of_mem _ y.2
  exact le_csSup hb (mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)

theorem SingularCComponent.contains_connected_region {g : RiemannianMetric 3 M}
    {D : LeviCivitaData g} {C : ℝ} (N : SingularCComponent g D C)
    {W : Set M} (hW : IsPreconnected W) {x : M}
    (hx : x ∈ W) (hNx : x ∈ N.carrier) : W ⊆ N.carrier := by
  rw [N.component_eq] at hNx ⊢
  rw [connectedComponent_eq hNx]
  exact hW.subset_connectedComponent hx

theorem not_component_of_collar_plane {g : RiemannianMetric 3 M}
    {D : LeviCivitaData g} {C : ℝ} {W : Set M} (hW : IsPreconnected W)
    (hscalar : Continuous D.scalarCurvature) {p : M} (hp : p ∈ W)
    (v w : TangentSpace (𝓡 3) p)
    (horth : LeviCivitaData.IsOrthonormalPair g p v w)
    (hplane : D.sectionalCurvature p v w ≤ C⁻¹ * D.scalarCurvature p)
    {x : M} (hx : x ∈ W) :
    ¬ ∃ N : SingularCComponent g D C, x ∈ N.carrier := by
  rintro ⟨N, hNx⟩
  have hNp := N.contains_connected_region hW hx hNx hp
  have hsup := N.scalar_le_sup hscalar.continuousOn hNp
  have hlower := N.sectional_lower p hNp v w horth
  have hscale := mul_le_mul_of_nonneg_left hsup (inv_nonneg.mpr N.constant_pos.le)
  exact (not_lt_of_ge (hplane.trans hscale)) hlower

end PoincareConjecture
