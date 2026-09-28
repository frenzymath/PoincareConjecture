import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Frame.Chart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartField_transition
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f f.source)
    (hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f.symm f.target)
    {p : ℝ × ℝ} (hp : p ∈ f.target) (hx : f.symm p ∈ e.source) (v : ℝ × ℝ) :
    mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) f (fun _ => v) (f.symm p) =
      mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e
        (fun _ => fderiv ℝ (fun q : ℝ × ℝ => e (f.symm q)) p v) (f.symm p) := by
  have heD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hfD : f.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨hf.mdifferentiableOn (by simp), hfi.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (f.symm p)).IsInvertible :=
    ⟨heD.mfderiv hx, rfl⟩
  rw [LeviCivitaData.chartField_symm_apply f hf hfi hp]
  apply heD.mfderiv_injective hx
  simp only [mpullback, hinv.self_apply_inverse]
  have h := congrArg (fun L => L v) (mfderiv_comp p
    (heD.mdifferentiableAt hx) (hfD.mdifferentiableAt_symm hp))
  dsimp only [TangentSpace] at h ⊢
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, Function.comp_def] using h.symm

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartField_eq_coordinates
    (e : OpenPartialHomeomorph S (ℝ × ℝ)) (x : S) (v : ℝ × ℝ) :
    mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) x =
      v.1 • mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x +
      v.2 • mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1)) x := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  unfold mpullback
  conv_lhs => rw [hv, map_add, map_smul, map_smul]

theorem chartTriangle_frameOrientation_mul_tangent_neg
    (g : RiemannianMetric 2 S) (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f f.source)
    (hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f.symm f.target)
    (Q : RiemannianMetric.AlignedChartFrame g e) (R : RiemannianMetric.AlignedChartFrame g f)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hea : (0, a) ∈ e.target) (hfb : (0, b) ∈ f.target)
    (hpoint : e.symm (0, a) = f.symm (0, b))
    (hdisjoint : Disjoint
      (e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      (f.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}))
    (hboundary : ∀ᶠ s in 𝓝 b, (e (f.symm (0, s))).1 = 0) :
    let x := f.symm (0, b)
    g.frameOrientation x (Q.first x) (Q.second x) (R.first x) (R.second x) *
      (fderiv ℝ (fun p : ℝ × ℝ => e (f.symm p)) (0, b) (0, 1)).2 < 0 := by
  let x := f.symm (0, b)
  let L := fderiv ℝ (fun p : ℝ × ℝ => e (f.symm p)) (0, b)
  let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1)) x
  let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) f (fun _ => (1, 0)) x
  let W := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) f (fun _ => (0, 1)) x
  have hx : x ∈ e.source := by
    change f.symm (0, b) ∈ e.source
    rw [← hpoint]
    exact e.map_target hea
  have hx' : x ∈ f.source := f.map_target hfb
  have heD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hfD : f.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨hf.mdifferentiableOn (by simp), hfi.mdifferentiableOn (by simp)⟩
  have hn : (L (1, 0)).1 < 0 :=
    chartTriangle_transverse_deriv_neg e f heD hfD ha hb hea hfb hpoint hdisjoint hboundary
  have hL : HasFDerivAt (fun p : ℝ × ℝ => e (f.symm p)) L (0, b) :=
    (((heD.mdifferentiableAt hx).comp (0, b)
      (hfD.mdifferentiableAt_symm hfb)).differentiableAt).hasFDerivAt
  have htan : HasDerivAt (fun s : ℝ => (e (f.symm (0, s))).1) (L (0, 1)).1 b := by
    have h := hL.comp_hasDerivAt b ((hasDerivAt_const b (0 : ℝ)).prodMk (hasDerivAt_id b))
    exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt b h
  have htan0 : (L (0, 1)).1 = 0 :=
    htan.unique ((hasDerivAt_const b (0 : ℝ)).congr_of_eventuallyEq hboundary)
  have hV : V = (L (1, 0)).1 • X + (L (1, 0)).2 • Y := by
    rw [show V = mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => L (1, 0)) x from
      chartField_transition e f he hei hf hfi hfb hx (1, 0)]
    exact chartField_eq_coordinates e x (L (1, 0))
  have hW : W = (L (0, 1)).2 • Y := by
    rw [show W = mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => L (0, 1)) x from
      chartField_transition e f he hei hf hfi hfb hx (0, 1), chartField_eq_coordinates, htan0,
      zero_smul, zero_add]
  have hk : (L (0, 1)).2 ≠ 0 := by
    intro hk
    have hne := LeviCivitaData.chartField_ne_zero f hf hfi
      (show ((0, 1) : ℝ × ℝ) ≠ 0 by norm_num) hx'
    change W ≠ 0 at hne
    exact hne (by rw [hW, hk, zero_smul])
  let P := g.frameOrientation x (Q.first x) (Q.second x) X Y
  let N := g.frameOrientation x (R.first x) (R.second x) V W
  let δ := g.frameOrientation x (Q.first x) (Q.second x) (R.first x) (R.second x)
  have hP : 0 < P := Q.positive x hx
  have hN : 0 < N := R.positive x hx'
  have hchange := g.frameOrientation_change x (Q.first x) (Q.second x)
    (R.unit_first x hx') (R.unit_second x hx') (R.orthogonal x hx') V W
  have hdet : N * δ = (L (1, 0)).1 * (L (0, 1)).2 * P := by
    rw [← hchange, hV, hW]
    simp only [P, RiemannianMetric.frameOrientation, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    ring
  have hnegative : N * (δ * (L (0, 1)).2) < 0 := by
    have h := mul_neg_of_neg_of_pos hn (mul_pos (sq_pos_of_ne_zero hk) hP)
    calc
      N * (δ * (L (0, 1)).2) = (L (1, 0)).1 * ((L (0, 1)).2 ^ 2 * P) := by
        rw [← mul_assoc, hdet]
        ring
      _ < 0 := h
  change δ * (L (0, 1)).2 < 0
  by_contra h
  exact (not_lt_of_ge (mul_nonneg hN.le (le_of_not_gt h))) hnegative

end PoincareConjecture.Topology.Surface
