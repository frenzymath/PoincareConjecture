import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeFrame
import PoincareConjecture.Proofs.M09.ChartVectorField










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



def productChartField (C : SpacetimeCharts n M a b)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (q : C.Point) : TangentSpace (𝓡 (n + 1)) q :=
  C.horizontal q (PoincareConjecture.Proofs.M09.chartVectorField p v q.1) +
    r • C.timeVector q


theorem productChartField_split (C : SpacetimeCharts n M a b)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) (q : C.Point) :
    C.split q (C.productChartField p v r q) =
      (PoincareConjecture.Proofs.M09.chartVectorField p v q.1, r) := by
  simp [productChartField, horizontal, timeVector]



theorem productChartField_eq_mpullback (C : SpacetimeCharts n M a b)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) (q : C.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    C.productChartField p v r q =
      VectorField.mpullback (𝓡 (n + 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (fun z : C.Point =>
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) z.1, (z.2 : ℝ)))
        (fun _ => (v, r)) q := by
  let := C.chartedSpace
  let E := EuclideanSpace ℝ (Fin n)
  let psi : C.Point → E × ℝ := fun z => ((chartAt E p) z.1, (z.2 : ℝ))
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (chartAt E p) q.1 :=
    contMDiffOn_chart.contMDiffAt ((chartAt E p).open_source.mem_nhds hq)
  have hpsi : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ∞ psi q :=
    (hc.comp q (C.contMDiff_space q)).prodMk_space (C.contMDiff_clock q)
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hq
  let D : TangentSpace (𝓡 (n + 1)) q ≃L[ℝ] E × ℝ :=
    (C.split q).trans (L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  have hD : mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) psi q =
      D.toContinuousLinearMap := by
    ext V
    apply Prod.ext
    · have hfst : MDifferentiableAt 𝓘(ℝ, E × ℝ) (𝓡 n)
          (Prod.fst : E × ℝ → E) (psi q) :=
        differentiableAt_fst.mdifferentiableAt
      have h := mfderiv_comp_apply (f := psi) (g := (Prod.fst : E × ℝ → E))
        q hfst (hpsi.mdifferentiableAt (by simp)) V
      have hsp := mfderiv_comp_apply (f := fun z : C.Point => z.1)
        (g := chartAt E p) q (hc.mdifferentiableAt (by simp))
        (C.contMDiff_space.mdifferentiableAt (by simp)) V
      have hfst' : (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) psi q V).1 =
          mfderiv (𝓡 (n + 1)) (𝓡 n) (fun z : C.Point => (chartAt E p) z.1) q V := by
        simpa +instances only [mfderiv_eq_fderiv, fderiv_fst,
          ContinuousLinearMap.coe_fst', Function.comp_def, psi] using! h.symm
      rw [hfst']
      change _ = mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q.1 (C.split q V).1
      rw [C.split_space]
      exact hsp
    · have hsnd : MDifferentiableAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ)
          (Prod.snd : E × ℝ → ℝ) (psi q) :=
        differentiableAt_snd.mdifferentiableAt
      have h := mfderiv_comp_apply (f := psi) (g := (Prod.snd : E × ℝ → ℝ))
        q hsnd (hpsi.mdifferentiableAt (by simp)) V
      change (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) psi q V).2 = (C.split q V).2
      rw [C.split_time]
      simpa +instances only [mfderiv_eq_fderiv, fderiv_snd,
        ContinuousLinearMap.coe_snd', Function.comp_def, psi] using! h.symm
  change C.productChartField p v r q =
    (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) psi q).inverse (v, r)
  rw [hD, ContinuousLinearMap.inverse_equiv]
  apply D.injective
  erw [D.apply_symm_apply]
  change (L (C.split q (C.productChartField p v r q)).1,
    (C.split q (C.productChartField p v r q)).2) = (v, r)
  rw [C.productChartField_split]
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q.1).IsInvertible := ⟨L, rfl⟩
  change ((mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q.1)
    ((mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q.1).inverse v), r) = (v, r)
  rw [hi.self_apply_inverse]



theorem productChartField_contMDiffOn (C : SpacetimeCharts n M a b)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (fun q : C.Point =>
        (⟨q, C.productChartField p v r q⟩ : TangentBundle (𝓡 (n + 1)) C.Point))
      {q : C.Point | q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source} := by
  let := C.chartedSpace
  intro q hq
  let B := PoincareConjecture.Proofs.M09.chartVectorField p v
  have hB : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% B) q.1 :=
    (PoincareConjecture.Proofs.M09.chartVectorField_smooth p v).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hq)
  have hzero : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)).tangent ∞
      (fun z : SpacetimeCarrier M a b =>
        (⟨z.2, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) (OpenTime a b))) :=
    (contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) : OpenTime a b → Type _)).comp
      contMDiff_snd
  have hprod : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun z : SpacetimeCarrier M a b =>
        (⟨z, (B z.1, 0)⟩ : TangentBundle ((𝓡 n).prod 𝓘(ℝ, ℝ))
          (SpacetimeCarrier M a b))) q :=
    contMDiff_equivTangentBundleProd_symm.contMDiffAt.comp q
      ((hB.comp q contMDiffAt_fst).prodMk (hzero q))
  have h := ((C.from_product_smooth.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp
    q hprod).comp q (C.to_product_smooth q)
  have hH : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (fun z : C.Point =>
        (⟨z, C.horizontal z (B z.1)⟩ : TangentBundle (𝓡 (n + 1)) C.Point)) q := by
    apply h.congr_of_eventuallyEq
    filter_upwards [] with z
    dsimp only [Function.comp_apply, id_eq, tangentMap]
    rw [TotalSpace.mk_inj]
    apply (C.split z).injective
    erw [C.split_mfderiv_from_product]
    exact (C.split z).apply_symm_apply (B z.1, 0)
  exact (hH.add_section ((C.timeVector_smooth q).const_smul_section (a := r))).contMDiffWithinAt



theorem productChartField_bracket (C : SpacetimeCharts n M a b)
    (p : M) (v w : EuclideanSpace ℝ (Fin n)) (r s : ℝ) (q : C.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    VectorField.mlieBracket (𝓡 (n + 1))
      (C.productChartField p v r) (C.productChartField p w s) q = 0 := by
  let := C.chartedSpace
  let E := EuclideanSpace ℝ (Fin n)
  let psi : C.Point → E × ℝ := fun z => ((chartAt E p) z.1, (z.2 : ℝ))
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (chartAt E p) q.1 :=
    contMDiffOn_chart.contMDiffAt ((chartAt E p).open_source.mem_nhds hq)
  have hpsi : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) ∞ psi q :=
    (hc.comp q (C.contMDiff_space q)).prodMk_space (C.contMDiff_clock q)
  have horder : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  let : IsManifold (𝓡 (n + 1)) (minSmoothness ℝ 2) C.Point :=
    IsManifold.of_le (n := ∞) horder
  have hconst (u : E × ℝ) : ContMDiff 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E × ℝ)).tangent ∞
      (fun z : E × ℝ => (⟨z, u⟩ : TangentBundle 𝓘(ℝ, E × ℝ) (E × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have h := VectorField.mpullback_mlieBracket
    ((hconst (v, r) (psi q)).mdifferentiableAt (by simp))
    ((hconst (w, s) (psi q)).mdifferentiableAt (by simp)) hpsi horder
  have hz : VectorField.mlieBracket 𝓘(ℝ, E × ℝ)
      (fun _ : E × ℝ => (v, r)) (fun _ : E × ℝ => (w, s)) = 0 := by
    change VectorField.mlieBracketWithin 𝓘(ℝ, E × ℝ)
      (fun _ : E × ℝ => (v, r)) (fun _ : E × ℝ => (w, s)) univ = 0
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    ext z <;> simp [VectorField.lieBracketWithin]
  have hnear : ∀ᶠ z : C.Point in 𝓝 q, z.1 ∈ (chartAt E p).source :=
    C.contMDiff_space.continuous.continuousAt
      ((chartAt E p).open_source.mem_nhds hq)
  have heq (u : E) (t : ℝ) : C.productChartField p u t =ᶠ[𝓝 q]
      VectorField.mpullback (𝓡 (n + 1)) 𝓘(ℝ, E × ℝ) psi (fun _ => (u, t)) := by
    filter_upwards [hnear] with z hz
    exact C.productChartField_eq_mpullback p u t z hz
  rw [(heq v r).mlieBracket_vectorField_eq (heq w s), ← h, hz,
    VectorField.mpullback_zero]
  rfl

end PoincareConjecture.M62.SpacetimeCharts
