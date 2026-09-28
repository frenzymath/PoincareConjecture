import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartFrame
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorField.LieBracket










set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def chartVectorField (p : M) (v : E) :
    (x : M) → TangentSpace (𝓡 n) x :=
  VectorField.mpullback (𝓡 n) (𝓡 n) (chartAt E p) (fun _ ↦ v)

theorem chartVectorField_smooth (p : M) (v : E) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (chartVectorField p v))
      (chartAt E p).source := by
  have hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : E ↦ (⟨y, v⟩ : TangentBundle (𝓡 n) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E ↦ v)).mpr contDiff_const
  intro x hx
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (chartAt E p) x :=
    contMDiffOn_chart.contMDiffAt ((chartAt E p).open_source.mem_nhds hx)
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) x).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hx, rfl⟩
  exact ((hV _).mpullback_vectorField_preimage hc hi (by simp)).contMDiffWithinAt

theorem chartVectorField_at_inverse (p : M) (v : E) (y : E)
    (hy : y ∈ (chartAt E p).target) :
    chartVectorField p v ((chartAt E p).symm y) =
      mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v := by
  let e := chartAt E p
  have hi : (mfderiv (𝓡 n) (𝓡 n) e (e.symm y)).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv (e.map_target hy), rfl⟩
  have hcomp := congrArg (fun L : E →L[ℝ] E ↦ L v)
    ((mdifferentiable_chart (I := 𝓡 n) p).comp_symm_deriv hy)
  change (mfderiv (𝓡 n) (𝓡 n) e (e.symm y)).inverse v = _
  change (mfderiv (𝓡 n) (𝓡 n) e (e.symm y))
    ((mfderiv (𝓡 n) (𝓡 n) e.symm y) v) = v at hcomp
  calc
    _ = (mfderiv (𝓡 n) (𝓡 n) e (e.symm y)).inverse
        ((mfderiv (𝓡 n) (𝓡 n) e (e.symm y))
          ((mfderiv (𝓡 n) (𝓡 n) e.symm y) v)) := congrArg _ hcomp.symm
    _ = _ := hi.inverse_apply_self _

set_option backward.isDefEq.respectTransparency false in
theorem chartVectorField_bracket (p : M) (v w : E) (x : M)
    (hx : x ∈ (chartAt E p).source) :
    VectorField.mlieBracket (𝓡 n) (chartVectorField p v) (chartVectorField p w) x = 0 := by
  have horder : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) horder
  have hV (a : E) : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : E ↦ (⟨y, a⟩ : TangentBundle (𝓡 n) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E ↦ a)).mpr contDiff_const
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (chartAt E p) x :=
    contMDiffOn_chart.contMDiffAt ((chartAt E p).open_source.mem_nhds hx)
  have h := VectorField.mpullback_mlieBracket
    ((hV v _).mdifferentiableAt (by simp)) ((hV w _).mdifferentiableAt (by simp))
    hc horder
  have hz : VectorField.mlieBracket (𝓡 n) (fun _ : E ↦ v) (fun _ : E ↦ w) = 0 := by
    change VectorField.mlieBracketWithin (𝓘(ℝ, E)) (fun _ : E ↦ v)
      (fun _ : E ↦ w) Set.univ = 0
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    ext y
    simp [VectorField.lieBracketWithin]
  change VectorField.mlieBracket (𝓡 n)
    (VectorField.mpullback (𝓡 n) (𝓡 n) (chartAt E p) (fun _ ↦ v))
    (VectorField.mpullback (𝓡 n) (𝓡 n) (chartAt E p) (fun _ ↦ w)) x = 0
  rw [← h, hz, VectorField.mpullback_zero]
  rfl

theorem mvfderiv_chartVectorField (p : M) (f : M → ℝ) (y v : E)
    (hy : y ∈ (chartAt E p).target)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f ((chartAt E p).symm y)) :
    mvfderiv (𝓡 n) f ((chartAt E p).symm y)
        (chartVectorField p v ((chartAt E p).symm y)) =
      fderiv ℝ (fun z ↦ f ((chartAt E p).symm z)) y v := by
  rw [chartVectorField_at_inverse p v y hy]
  have h := mfderiv_comp y hf
    ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at h
  exact (congrArg (fun L ↦ L v) h).symm

theorem chartVectorField_differential (p x : M) (v : TangentSpace (𝓡 n) x)
    (hx : x ∈ (chartAt E p).source) :
    chartVectorField p (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) x v) x = v := by
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) x).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hx, rfl⟩
  exact hi.inverse_apply_self v

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
