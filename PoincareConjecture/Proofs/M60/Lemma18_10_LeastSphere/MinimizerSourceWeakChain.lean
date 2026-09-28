import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactWeakChain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem suFinAddEquivProd_symm_left {n m : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm (x, y) (Fin.castAdd m i) = x i := by
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    PiLp.sumPiLpEquivProdLpPiLp, WithLp.prodContinuousLinearEquiv,
    WithLp.linearEquiv, finSumFinEquiv]
  rfl

theorem suFinAddEquivProd_symm_right {n m : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm (x, y) (Fin.natAdd n i) = y i := by
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    PiLp.sumPiLpEquivProdLpPiLp, WithLp.prodContinuousLinearEquiv,
    WithLp.linearEquiv, finSumFinEquiv]
  rfl

theorem suWeakPartial_source_comp_on_compact {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {W : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {a : Plane} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : MemLp u 4 (volume.restrict (Metric.ball a R)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun x => W i x b) (fun x => u x b)
      (Metric.ball a R))
    {O K : Set (Plane × EuclideanSpace ℝ (Fin m))}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hmap : MapsTo (fun x => (x, u x)) (Metric.closedBall a R) K)
    {F : (Plane × EuclideanSpace ℝ (Fin m)) → ℝ} (hF : ContDiffOn ℝ 1 F O)
    (i : Fin 2) :
    HasWeakPartialDeriv i
      (fun x => fderiv ℝ F (x, u x) (EuclideanSpace.single i 1, W i x))
      (fun x => F (x, u x)) (Metric.ball a r) := by
  let e : EuclideanSpace ℝ (Fin (2 + m)) ≃L[ℝ] Plane × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let U : Plane → EuclideanSpace ℝ (Fin (2 + m)) := fun x => e.symm (x, u x)
  let Q : Fin 2 → Plane → EuclideanSpace ℝ (Fin (2 + m)) :=
    fun j x => e.symm (EuclideanSpace.single j 1, W j x)
  let : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a R) < ⊤)⟩
  have hU : MemLp U 4 (volume.restrict (Metric.ball a R)) :=
    e.symm.toContinuousLinearMap.comp_memLp'
      (memLp_prod_iff.mpr ⟨suContinuous_memLp_ball continuousOn_id, hu⟩)
  have hQ (j : Fin 2) : MemLp (Q j) 2 (volume.restrict (Metric.ball a R)) :=
    e.symm.toContinuousLinearMap.comp_memLp'
      (memLp_prod_iff.mpr ⟨memLp_const _, hW j⟩)
  have hwQ (j : Fin 2) (b : Fin (2 + m)) :
      HasWeakPartialDeriv j (fun x => Q j x b) (fun x => U x b) (Metric.ball a R) := by
    cases b using Fin.addCases with
    | left k =>
      simp only [Q, U, e, suFinAddEquivProd_symm_left]
      have ht := HasWeakPartialDeriv.of_contDiff (i := j)
        (Ω := Metric.ball a R) Metric.isOpen_ball
        ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff : ContDiff ℝ 1 _)
      simpa only [HasWeakPartialDeriv, ContinuousLinearMap.fderiv, PiLp.proj_apply] using ht
    | right k =>
      simpa only [Q, U, e, suFinAddEquivProd_symm_right] using hw j k
  have hKe : IsCompact (e.symm '' K) := hK.image e.symm.continuous
  have hKeO : e.symm '' K ⊆ e ⁻¹' O := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [mem_preimage, e.apply_symm_apply] using hKO hz
  have hUmap : MapsTo U (Metric.closedBall a R) (e.symm '' K) :=
    fun x hx => mem_image_of_mem _ (hmap hx)
  have hFc : ContDiffOn ℝ 1 (F ∘ e) (e ⁻¹' O) :=
    hF.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have ht := suWeakPartial_comp_on_compact hr hrR hU hQ hwQ
    (hO.preimage e.continuous) hKe hKeO hUmap hFc i
  have he (x : Plane) : fderiv ℝ (F ∘ e) (U x) (Q i x) =
      fderiv ℝ F (x, u x) (EuclideanSpace.single i 1, W i x) := by
    rw [e.comp_right_fderiv]
    simp [U, Q]
  simpa only [he, Function.comp_apply, U, e.apply_symm_apply] using ht

end PoincareConjecture.M60

end
