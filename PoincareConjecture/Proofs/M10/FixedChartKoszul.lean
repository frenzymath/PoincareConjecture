import PoincareConjecture.Proofs.M10.FixedChartHessian










set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem fixedChartFields_mlieBracket_eq_zero (q₀ : M)
    (v w : TangentSpace (𝓡 n) q₀) {q : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source) :
    VectorField.mlieBracket (𝓡 n)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) q = 0 := by
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) 2 M)
  let e := extChartAt (𝓡 n) q₀
  have hqe : q ∈ e.source := by simpa only [e, extChartAt_source] using hq
  have hy : e q ∈ e.target := e.map_source hqe
  have hg (a : TangentSpace (𝓡 n) q₀) :
      VectorField.mpullback (𝓡 n) (𝓡 n) e.symm
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) =ᶠ[𝓝 (e q)]
          (fun _ ↦ a) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy] with y hy'
    simpa only [VectorField.mpullbackWithin_univ] using preferredField_pullback q₀ a hy'
  have hv := (preferredField_contMDiffAt_of_mem q₀ v hq).mdifferentiableAt (by simp)
  have hw := (preferredField_contMDiffAt_of_mem q₀ w hq).mdifferentiableAt (by simp)
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm (e q) :=
    (contMDiffOn_extChartAt_symm q₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)
  have hb := VectorField.mpullback_mlieBracket (f := e.symm) (x₀ := e q)
    (V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w)
    (by simpa only [e.left_inv hqe] using hv)
    (by simpa only [e.left_inv hqe] using hw) hi
    (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hzero : VectorField.mlieBracket (𝓡 n)
      (VectorField.mpullback (𝓡 n) (𝓡 n) e.symm
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v))
      (VectorField.mpullback (𝓡 n) (𝓡 n) e.symm
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w)) (e q) = 0 := by
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ,
      (hg v).lieBracket_vectorField_eq (hg w)]
    simp [VectorField.lieBracket]
  rw [hzero, VectorField.mpullback_apply] at hb
  have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) hy
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hinv
  have hz := hinv.inverse_apply_eq.mp hb
  change VectorField.mlieBracket (𝓡 n)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) (e.symm (e q)) = _ at hz
  rw [e.left_inv hqe] at hz
  simpa only [map_zero] using hz

set_option backward.isDefEq.respectTransparency false in

theorem fixedChart_diagonal_koszul (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (q₀ : M) (v w : TangentSpace (𝓡 n) q₀) {q : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source) :
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
    2 * g.inner q (D.connection X q (X q)) (Y q) =
      2 * mvfderiv (𝓡 n) (fun x ↦ g.inner x (X x) (Y x)) q (X q) -
        mvfderiv (𝓡 n) (fun x ↦ g.inner x (X x) (X x)) q (Y q) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hv := (preferredField_contMDiffAt_of_mem q₀ v hq).mdifferentiableAt (by simp)
  have hw := (preferredField_contMDiffAt_of_mem q₀ w hq).mdifferentiableAt (by simp)
  have h₁ := D.metricCompatible.mvfderiv_inner_eq X hv hw
  have h₂ := D.metricCompatible.mvfderiv_inner_eq Y hv hv
  have ht := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hv hw
  rw [fixedChartFields_mlieBracket_eq_zero q₀ v w hq] at ht
  have hconn := sub_eq_zero.mp ht
  change mvfderiv (𝓡 n) (fun x ↦ g.inner x (X x) (Y x)) q (X q) =
    g.inner q (D.connection X q (X q)) (Y q) +
      g.inner q (X q) (D.connection Y q (X q)) at h₁
  change mvfderiv (𝓡 n) (fun x ↦ g.inner x (X x) (X x)) q (Y q) =
    g.inner q (D.connection X q (Y q)) (X q) +
      g.inner q (X q) (D.connection X q (Y q)) at h₂
  rw [g.symm q _ (X q)] at h₂
  change D.connection Y q (X q) = D.connection X q (Y q) at hconn
  rw [hconn] at h₁
  dsimp only
  change 2 * g.inner q (D.connection X q (X q)) (Y q) = _
  linarith

end PoincareConjecture.M10
