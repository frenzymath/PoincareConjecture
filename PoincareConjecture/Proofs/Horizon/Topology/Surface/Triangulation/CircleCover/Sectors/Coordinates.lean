


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Basic








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch

private noncomputable def signEquiv (i : Bool) : ℝ ≃L[ℝ] ℝ :=
  if i then ContinuousLinearEquiv.refl ℝ ℝ else ContinuousLinearEquiv.neg ℝ


noncomputable def sectorParameterEquiv (c : ℝ × ℝ) (i : Bool × Bool) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  ((signEquiv i.1).prodCongr (signEquiv i.2)).toHomeomorph.trans (Homeomorph.addRight c)

theorem sectorParameterEquiv_apply (c q : ℝ × ℝ) (i : Bool × Bool) :
    sectorParameterEquiv c i q =
      ((if i.1 then q.1 else -q.1) + c.1, (if i.2 then q.2 else -q.2) + c.2) := by
  rcases i with ⟨i, j⟩
  cases i <;> cases j <;> rfl

theorem sectorParameterEquiv_zero (c : ℝ × ℝ) (i : Bool × Bool) :
    sectorParameterEquiv c i 0 = c := by simp [sectorParameterEquiv_apply]

theorem contDiff_sectorParameterEquiv (c : ℝ × ℝ) (i : Bool × Bool) :
    ContDiff ℝ ∞ (sectorParameterEquiv c i) :=
  ((signEquiv i.1).prodCongr (signEquiv i.2)).contDiff.add contDiff_const

theorem contDiff_sectorParameterEquiv_symm (c : ℝ × ℝ) (i : Bool × Bool) :
    ContDiff ℝ ∞ (sectorParameterEquiv c i).symm :=
  ((signEquiv i.1).prodCongr (signEquiv i.2)).symm.contDiff.comp
    (contDiff_id.sub contDiff_const)

private theorem image_signed_interval (c w : ℝ) (i : Bool) :
    (fun x => (if i then x else -x) + c) '' Icc (0 : ℝ) w =
      closedSectorInterval c w i := by
  cases i <;> ext y <;> constructor
  · rintro ⟨x, hx, rfl⟩
    constructor <;> dsimp at * <;> linarith [hx.1, hx.2]
  · intro hy
    refine ⟨c - y, ⟨?_, ?_⟩, ?_⟩
    · exact sub_nonneg.mpr hy.2
    · linarith [hy.1]
    · dsimp; ring
  · rintro ⟨x, hx, rfl⟩
    constructor <;> dsimp at * <;> linarith [hx.1, hx.2]
  · intro hy
    refine ⟨y - c, ⟨?_, ?_⟩, ?_⟩
    · exact sub_nonneg.mpr hy.1
    · linarith [hy.2]
    · dsimp; ring

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  {r : M → ℝ} {p : M}
variable (P : ChartCircleArrangementVertexPatch r p)

theorem sectorParameterEquiv_image_square (i : Bool × Bool) :
    sectorParameterEquiv P.center i '' (Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width) =
      P.closedSectorBox i := by
  simp only [sectorParameterEquiv_apply, closedSectorBox]
  simpa only [image_signed_interval] using
    (prod_image_image_eq (s := Icc (0 : ℝ) P.width) (t := Icc (0 : ℝ) P.width)
      (m₁ := fun x => (if i.1 then x else -x) + P.center.1)
      (m₂ := fun x => (if i.2 then x else -x) + P.center.2)).symm


noncomputable def sectorCoordinates (i : Bool × Bool) : OpenPartialHomeomorph (ℝ × ℝ) M :=
  (sectorParameterEquiv P.center i).toOpenPartialHomeomorph.trans P.productCoordinates

theorem sectorCoordinates_square_source (i : Bool × Bool) :
    Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width ⊆ (P.sectorCoordinates i).source := by
  intro q hq
  refine ⟨mem_univ _, P.closedSectorBox_subset_source i ?_⟩
  rw [← P.sectorParameterEquiv_image_square i]
  exact mem_image_of_mem _ hq

theorem sectorCoordinates_image_square (i : Bool × Bool) :
    P.sectorCoordinates i '' (Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width) =
      P.closedSector i := by
  calc
    _ = P.productCoordinates '' (sectorParameterEquiv P.center i ''
        (Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width)) := (image_image _ _ _).symm
    _ = P.closedSector i := congrArg (fun S => P.productCoordinates '' S)
      (P.sectorParameterEquiv_image_square i)

theorem sectorCoordinates_zero (i : Bool × Bool) : P.sectorCoordinates i 0 = p := by
  change P.coordinates (collarParameterEquiv.symm (sectorParameterEquiv P.center i 0)) = p
  rw [sectorParameterEquiv_zero, ← P.center_eq]
  exact P.coordinates.right_inv (P.carrier_subset_target
    (P.openCarrier_subset_carrier P.mem_openCarrier))

theorem sectorCoordinates_smooth (i : Bool × Bool) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (P.sectorCoordinates i)
      (P.sectorCoordinates i).source := by
  have hA : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (collarParameterEquiv.symm ∘ sectorParameterEquiv P.center i)
      (P.sectorCoordinates i).source := (collarParameterEquiv.symm.contDiff.comp
        (contDiff_sectorParameterEquiv P.center i)).contMDiff.contMDiffOn
  exact P.smooth.comp hA (fun _ hq => hq.2.2)

theorem sectorCoordinates_smooth_symm (i : Bool × Bool) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (P.sectorCoordinates i).symm
      (P.sectorCoordinates i).target := by
  have hA := ((contDiff_sectorParameterEquiv_symm P.center i).comp
    collarParameterEquiv.contDiff).contMDiff
  exact hA.comp_contMDiffOn (P.smooth_symm.mono (fun _ hq => hq.1.1))


noncomputable def chartSectorCoordinates (x : M) (i : Bool × Bool) :
    OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)) :=
  (P.sectorCoordinates i).trans (chartAt (EuclideanSpace ℝ (Fin 2)) x)

theorem chartSectorCoordinates_square_source (x : M) (i : Bool × Bool)
    (hchart : P.closedSector i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) :
    Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width ⊆
      (P.chartSectorCoordinates x i).source := by
  intro q hq
  refine ⟨P.sectorCoordinates_square_source i hq, hchart ?_⟩
  rw [← P.sectorCoordinates_image_square i]
  exact mem_image_of_mem _ hq

theorem chartSectorCoordinates_zero (x : M) (i : Bool × Bool) :
    P.chartSectorCoordinates x i 0 = chartAt (EuclideanSpace ℝ (Fin 2)) x p := by
  change chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i 0) = _
  rw [P.sectorCoordinates_zero]

variable [IsManifold (𝓡 2) ∞ M]

theorem chartSectorCoordinates_smooth (x : M) (i : Bool × Bool) :
    ContDiffOn ℝ ∞ (P.chartSectorCoordinates x i) (P.chartSectorCoordinates x i).source := by
  exact ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := x)).comp
    ((P.sectorCoordinates_smooth i).mono (fun _ hq => hq.1))
      (fun _ hq => hq.2)).contDiffOn

theorem chartSectorCoordinates_smooth_symm (x : M) (i : Bool × Bool) :
    ContDiffOn ℝ ∞ (P.chartSectorCoordinates x i).symm
      (P.chartSectorCoordinates x i).target := by
  exact ((P.sectorCoordinates_smooth_symm i).comp
    ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := x)).mono (fun _ hq => hq.1))
      (fun _ hq => hq.2)).contDiffOn

end ChartCircleArrangementVertexPatch
end PoincareConjecture.Topology.Surface
