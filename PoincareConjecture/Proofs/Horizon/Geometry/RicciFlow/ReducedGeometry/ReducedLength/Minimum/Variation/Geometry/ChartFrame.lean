import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem squareTime_mem_interior_preimage {J : Set ℝ} {T s : ℝ}
    (ht : T - s ^ 2 ∈ interior J) :
    s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J) :=
  mem_interior_iff_mem_nhds.mpr
    ((continuous_const.sub (continuous_id.pow 2)).continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp ht))

noncomputable def chartFrame (x : M) (v : EuclideanSpace ℝ (Fin n))
    (y : M) : TangentSpace (𝓡 n) y :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL ℝ y v

theorem chartFrame_contMDiffOn (x : M) (v : EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (chartFrame x v y))
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hmap : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : M ↦ (y, v)) e.baseSet := contMDiffOn_id.prodMk contMDiffOn_const
  apply (e.contMDiffOn_symm.comp hmap (fun y hy ↦ e.mem_target.mpr hy)).congr
  intro y hy
  rw [show chartFrame x v y = e.symm y v from Bundle.Trivialization.symmL_apply e hy v]
  exact e.mk_symm hy v

theorem chartFrame_curve_contMDiffOn (x : M) (γ : ℝ → M)
    (v : ℝ → EuclideanSpace ℝ (Fin n)) (I : Set ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (hv : ContDiffOn ℝ ∞ v I)
    (hchart : ∀ s ∈ I, γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (γ s) (chartFrame x (v s) (γ s))) I := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hm : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (γ s, v s)) I := hγ.prodMk hv.contMDiffOn
  apply (e.contMDiffOn_symm.comp hm (fun s hs ↦ e.mem_target.mpr (hchart s hs))).congr
  intro s hs
  rw [show chartFrame x (v s) (γ s) = e.symm (γ s) (v s) from
    Bundle.Trivialization.symmL_apply e (hchart s hs) (v s)]
  exact e.mk_symm (hchart s hs) (v s)

theorem chartFrame_eq_mpullback {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    chartFrame x v y = VectorField.mpullback (𝓡 n) (𝓡 n)
      (extChartAt (𝓡 n) x) (fun _ ↦ v) y := by
  symm
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  apply (isInvertible_mfderiv_extChartAt (I := 𝓡 n) hy').inverse_apply_eq.mpr
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy]
  exact (Bundle.Trivialization.continuousLinearMapAt_symmL (R := ℝ)
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hy v).symm

theorem chartFrame_mlieBracket {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    VectorField.mlieBracket (𝓡 n) (chartFrame x v) (chartFrame x w) y = 0 := by
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := IsManifold.of_le htwo
  have heq (z : EuclideanSpace ℝ (Fin n)) : chartFrame x z =ᶠ[𝓝 y]
      VectorField.mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) (fun _ ↦ z) := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy] with p hp
    exact chartFrame_eq_mpullback hp z
  rw [(heq v).mlieBracket_vectorField_eq (heq w)]
  have hconst (z : EuclideanSpace ℝ (Fin n)) :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt
      (𝕜 := ℝ) (V := fun _ ↦ z) (x := extChartAt (𝓡 n) x y) (n := (1 : ℕ∞ω))).mpr
      contDiffAt_const).mdifferentiableAt one_ne_zero
  have hchart : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) x) y :=
    contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hy
  rw [← VectorField.mpullback_mlieBracket (hconst v) (hconst w)
    hchart htwo]
  have hzero : VectorField.mlieBracket (𝓡 n)
      (fun _ : EuclideanSpace ℝ (Fin n) ↦ v) (fun _ : EuclideanSpace ℝ (Fin n) ↦ w) = 0 := by
    funext q
    change VectorField.mlieBracketWithin (𝓡 n) (fun _ ↦ v) (fun _ ↦ w) univ q = 0
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    simp [VectorField.lieBracketWithin]
  rw [hzero, VectorField.mpullback_zero]
  rfl

theorem chartFrame_connection_diagonal (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.inner y (D.connection (chartFrame x v) y (chartFrame x v y)) (chartFrame x w y) =
      mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
        (chartFrame x v y) -
      (1 / 2 : ℝ) * mvfderiv (𝓡 n)
        (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x v p)) y (chartFrame x w y) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiff (z : EuclideanSpace ℝ (Fin n)) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (chartFrame x z p)) y :=
    ((chartFrame_contMDiffOn x z y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hcross : D.connection (chartFrame x w) y (chartFrame x v y) =
      D.connection (chartFrame x v) y (chartFrame x w y) := by
    have h := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero (hdiff v) (hdiff w)
    rw [chartFrame_mlieBracket hy v w] at h
    exact sub_eq_zero.mp h
  have h₁ := D.metricCompatible.mvfderiv_inner_eq (chartFrame x v) (hdiff v) (hdiff w)
  have h₂ := D.metricCompatible.mvfderiv_inner_eq (chartFrame x w) (hdiff v) (hdiff v)
  change mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
      (chartFrame x v y) =
      g.inner y (D.connection (chartFrame x v) y (chartFrame x v y)) (chartFrame x w y) +
      g.inner y (chartFrame x v y) (D.connection (chartFrame x w) y (chartFrame x v y)) at h₁
  change mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x v p)) y
      (chartFrame x w y) =
      g.inner y (D.connection (chartFrame x v) y (chartFrame x w y)) (chartFrame x v y) +
      g.inner y (chartFrame x v y) (D.connection (chartFrame x v) y (chartFrame x w y)) at h₂
  rw [hcross] at h₁
  rw [g.symm y (D.connection (chartFrame x v) y (chartFrame x w y)) (chartFrame x v y)] at h₂
  linarith

theorem chartFrame_inverse_derivative {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    chartFrame x v y = mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
      (extChartAt (𝓡 n) x y) v := by
  unfold chartFrame
  rw [TangentBundle.symmL_trivializationAt hy]
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
  rfl

theorem chart_scalar_fderiv_apply {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (f : M → ℝ) (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x y) v =
      mvfderiv (𝓡 n) f y (chartFrame x v y) := by
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have htarget : e y ∈ e.target := e.map_source hy'
  have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm (e y) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x _ htarget).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds htarget)
  have h := mvfderiv_comp_apply_of_eq (e y) hf (hinv.mdifferentiableAt (by simp))
    (e.left_inv hy') v
  change mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) (f ∘ e.symm) (e y) v =
    mvfderiv (𝓡 n) f y (mfderiv (𝓡 n) (𝓡 n) e.symm (e y) v) at h
  rw [mfderiv_eq_fderiv, ← chartFrame_inverse_derivative hy v] at h
  exact h

theorem chartActionMetric_time_derivative {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (ht : T - s ^ 2 ∈ interior J) (v w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x y) v w)
      (4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) (chartFrame x w y)) s := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have heq : (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x y) v w) =
      (fun r ↦ (F.metric (T - r ^ 2)).inner y (chartFrame x v y) (chartFrame x w y)) := by
    funext r
    unfold chartActionMetric
    rw [(extChartAt (𝓡 n) x).left_inv hy', metricInChart_apply _ hy]
    rfl
  rw [heq]
  have hevol := (F.equation (T - s ^ 2) (interior_subset ht) y
    (chartFrame x v y) (chartFrame x w y)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
  have htime : HasDerivAt (fun r : ℝ ↦ T - r ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub T
  convert hevol.comp s htime using 1 <;> first | rfl | ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
