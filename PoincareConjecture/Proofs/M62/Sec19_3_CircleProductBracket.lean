import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductFrame
import Mathlib.Geometry.Manifold.VectorField.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.CircleProductCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {circumference : ℝ} {C : CircleGeometry circumference}

set_option maxHeartbeats 800000 in

theorem productChartField_bracket (P : CircleProductCharts C n M)
    (p : M) (v w : EuclideanSpace ℝ (Fin n)) (r s : ℝ) (q : P.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    VectorField.mlieBracket (𝓡 (n + 1))
      (P.productChartField p v r) (P.productChartField p w s) q = 0 := by
  let := P.chartedSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle circumference) := C.chartedSpace
  let : IsManifold (𝓡 1) ∞ (AddCircle circumference) := C.isManifold
  let E := EuclideanSpace ℝ (Fin n)
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞ (Prod.snd : P.Point → C.Point) :=
    contMDiff_snd.comp P.to_product_smooth
  obtain ⟨s₀, hs₀⟩ := QuotientAddGroup.mk_surjective q.2
  let hlocal := C.quotient_local_diffeomorph s₀
  let σ := hlocal.localInverse
  have hqσ : q.2 ∈ σ.source := by
    rw [← hs₀]
    exact hlocal.localInverse_mem_source
  have hσ (y : C.Point) (hy : y ∈ σ.source) :
      ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ σ y :=
    (hlocal.contmdiffOn_localInverse y hy).contMDiffAt (σ.open_source.mem_nhds hy)
  have hσframe (y : C.Point) (hy : y ∈ σ.source) :
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ y (C.frame y) = 1 := by
    have heq : (fun u : ℝ => σ (u : AddCircle circumference)) =ᶠ[𝓝 (σ y)] id := by
      filter_upwards [σ.open_target.mem_nhds (σ.map_source hy)] with u hu
      exact hlocal.localInverse_left_inv hu
    have hσ' : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) σ
        ((σ y : ℝ) : AddCircle circumference) := by
      rw [hlocal.localInverse_right_inv hy]
      exact (hσ y hy).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply
      (f := fun u : ℝ => (u : AddCircle circumference)) (g := σ) (σ y) hσ'
      (C.quotient_smooth.mdifferentiableAt (by simp)) 1
    have hv : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ ((σ y : ℝ) : AddCircle circumference)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun u : ℝ => (u : AddCircle circumference))
          (σ y) 1) = 1 := by
      rw [← hcomp]
      change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun u : ℝ => σ (u : AddCircle circumference)) (σ y)) 1 = 1
      rw [heq.mfderiv_eq, mfderiv_id]
      rfl
    rw [← C.frame_quotient, hlocal.localInverse_right_inv hy] at hv
    exact hv
  let ψ : P.Point → E × ℝ := fun z => ((chartAt E p) z.1, σ z.2)
  have hψ (z : P.Point) (hz : z.1 ∈ (chartAt E p).source) (hσz : z.2 ∈ σ.source) :
      ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ∞ ψ z :=
    ((contMDiffOn_chart.contMDiffAt ((chartAt E p).open_source.mem_nhds hz)).comp
      z (hfst z)).prodMk_space ((hσ z.2 hσz).comp z (hsnd z))
  have heq (u : E) (a : ℝ) (z : P.Point)
      (hz : z.1 ∈ (chartAt E p).source) (hσz : z.2 ∈ σ.source) :
      P.productChartField p u a z =
        VectorField.mpullback (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ψ (fun _ => (u, a)) z := by
    let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hz
    let K := (σ.isLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ hσz).mfderivToContinuousLinearEquiv
      (by simp)
    let D := (P.split z).trans (L.prodCongr K)
    have hD : mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ψ z = D.toContinuousLinearMap := by
      ext V
      apply Prod.ext
      · have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt E p) z.1 :=
          ((contMDiffOn_chart (I := 𝓡 n) (n := ∞)).contMDiffAt
            ((chartAt E p).open_source.mem_nhds hz)).mdifferentiableAt (by simp)
        have h := mfderiv_comp_apply (f := ψ) (g := (Prod.fst : E × ℝ → E)) z
          differentiableAt_fst.mdifferentiableAt ((hψ z hz hσz).mdifferentiableAt
            (by simp)) V
        have hp := mfderiv_comp_apply (f := (Prod.fst : P.Point → M))
          (g := chartAt E p) z hc (hfst.mdifferentiableAt (by simp)) V
        have hfirst : (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ψ z V).1 =
            mfderiv (𝓡 (n + 1)) (𝓡 n) (fun z : P.Point => (chartAt E p) z.1) z V := by
          simpa +instances only [mfderiv_eq_fderiv, fderiv_fst,
            ContinuousLinearMap.coe_fst', Function.comp_def, ψ] using! h.symm
        rw [hfirst]
        change _ = mfderiv (𝓡 n) (𝓡 n) (chartAt E p) z.1 (P.split z V).1
        rw [P.split_space]
        exact hp
      · have h := mfderiv_comp_apply (f := ψ) (g := (Prod.snd : E × ℝ → ℝ)) z
          differentiableAt_snd.mdifferentiableAt ((hψ z hz hσz).mdifferentiableAt
            (by simp)) V
        have hp := mfderiv_comp_apply (f := (Prod.snd : P.Point → C.Point))
          (g := σ) z ((hσ z.2 hσz).mdifferentiableAt (by simp))
          (hsnd.mdifferentiableAt (by simp)) V
        have hsecond : (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ψ z V).2 =
            mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (fun z : P.Point => σ z.2) z V := by
          simpa +instances only [mfderiv_eq_fderiv, fderiv_snd,
            ContinuousLinearMap.coe_snd', Function.comp_def, ψ] using! h.symm
        rw [hsecond]
        change _ = mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ z.2 (P.split z V).2
        rw [P.split_circle]
        exact hp
    change P.productChartField p u a z = (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ψ z).inverse _
    rw [hD, ContinuousLinearMap.inverse_equiv]
    apply D.injective
    erw [D.apply_symm_apply]
    change (L (P.split z (P.productChartField p u a z)).1,
      K (P.split z (P.productChartField p u a z)).2) = (u, a)
    rw [P.productChartField_split]
    apply Prod.ext
    · have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) z.1).IsInvertible := ⟨L, rfl⟩
      exact hi.self_apply_inverse u
    · change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ z.2 (a • C.frame z.2) = a
      rw [map_smul, hσframe z.2 hσz]
      exact mul_one a
  have horder : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  let : IsManifold (𝓡 (n + 1)) (minSmoothness ℝ 2) P.Point :=
    IsManifold.of_le (n := ∞) horder
  have hconst (u : E × ℝ) : ContMDiff 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E × ℝ)).tangent ∞
      (fun z : E × ℝ => (⟨z, u⟩ : TangentBundle 𝓘(ℝ, E × ℝ) (E × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hb := VectorField.mpullback_mlieBracket
    ((hconst (v, r) (ψ q)).mdifferentiableAt (by simp))
    ((hconst (w, s) (ψ q)).mdifferentiableAt (by simp)) (hψ q hq hqσ) horder
  have hzero : VectorField.mlieBracket 𝓘(ℝ, E × ℝ)
      (fun _ : E × ℝ => (v, r)) (fun _ : E × ℝ => (w, s)) = 0 := by
    change VectorField.mlieBracketWithin 𝓘(ℝ, E × ℝ)
      (fun _ : E × ℝ => (v, r)) (fun _ : E × ℝ => (w, s)) univ = 0
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    ext z <;> simp [VectorField.lieBracketWithin]
  have hbase : ∀ᶠ z : P.Point in 𝓝 q, z.1 ∈ (chartAt E p).source :=
    hfst.continuous.continuousAt ((chartAt E p).open_source.mem_nhds hq)
  have hcircle : ∀ᶠ z : P.Point in 𝓝 q, z.2 ∈ σ.source :=
    hsnd.continuous.continuousAt (σ.open_source.mem_nhds hqσ)
  have hnear (u : E) (a : ℝ) : P.productChartField p u a =ᶠ[𝓝 q]
      VectorField.mpullback (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ψ (fun _ => (u, a)) := by
    filter_upwards [hbase, hcircle] with z hz hσz
    exact heq u a z hz hσz
  rw [(hnear v r).mlieBracket_vectorField_eq (hnear w s), ← hb, hzero,
    VectorField.mpullback_zero]
  rfl

end PoincareConjecture.M62.CircleProductCharts
