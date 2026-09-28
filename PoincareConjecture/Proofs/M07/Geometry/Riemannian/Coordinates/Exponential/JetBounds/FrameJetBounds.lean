import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FrameRecurrence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CoframeEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialConnectionBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology BigOperators Manifold

namespace PoincareConjecture.CoordinateExponential

def scalarJetProductBound (q : ℕ) (A D : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |A i| * |D (q - i)|

def curvatureComponentSuccJetBound (n l q : ℕ) (A B C D : ℕ → ℝ) : ℝ :=
  n * scalarJetProductBound q A D + n * (4 + l) * scalarJetProductBound q B C

theorem scalarJetProductBound_nonneg (q : ℕ) (A D : ℕ → ℝ) :
    0 ≤ scalarJetProductBound q A D := by
  unfold scalarJetProductBound
  positivity

theorem curvatureComponentSuccJetBound_nonneg (n l q : ℕ) (A B C D : ℕ → ℝ) :
    0 ≤ curvatureComponentSuccJetBound n l q A B C D := by
  unfold curvatureComponentSuccJetBound
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (scalarJetProductBound_nonneg ..))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (scalarJetProductBound_nonneg ..))

section Calculus

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem norm_iteratedFDeriv_succ_le_of_directional
    {f : P → ℝ} {U : Set P} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : P} (hx : x ∈ U) (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ u, ‖iteratedFDeriv ℝ q (fun y => fderiv ℝ f y u) x‖ ≤ L * ‖u‖) :
    ‖iteratedFDeriv ℝ (q + 1) f x‖ ≤ L := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  apply ContinuousMultilinearMap.opNorm_le_bound hL
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL (Finset.prod_nonneg (by simp)))
  intro u
  have heq := iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hd
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl q) hx (u := u) (m := v)
  rw [iteratedFDerivWithin_of_isOpen q hU hx,
    iteratedFDerivWithin_of_isOpen q hU hx] at heq
  rw [← heq]
  calc
    ‖(iteratedFDeriv ℝ q (fun y => fderiv ℝ f y u) x) v‖ ≤
        ‖iteratedFDeriv ℝ q (fun y => fderiv ℝ f y u) x‖ * ∏ i, ‖v i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ (L * ‖u‖) * ∏ i, ‖v i‖ :=
      mul_le_mul_of_nonneg_right (h u) (Finset.prod_nonneg (by simp))
    _ = (L * ∏ i, ‖v i‖) * ‖u‖ := by ring

theorem norm_iteratedFDeriv_mul_le_scaled_bound
    {f g : P → ℝ} {U : Set P} (hU : IsOpen U) {q : ℕ}
    (hf : ContDiffOn ℝ q f U) (hg : ContDiffOn ℝ q g U)
    {x : P} (hx : x ∈ U) (A D : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i f x‖ ≤ A i * t)
    (hD : ∀ i ≤ q, ‖iteratedFDeriv ℝ i g x‖ ≤ D i) :
    ‖iteratedFDeriv ℝ q (fun y => f y * g y) x‖ ≤ scalarJetProductBound q A D * t := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  refine h.trans ?_
  rw [scalarJetProductBound, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hAi : ‖iteratedFDeriv ℝ i f x‖ ≤ |A i| * t :=
    (hA i hiq).trans (mul_le_mul_of_nonneg_right (le_abs_self _) ht)
  have hDi : ‖iteratedFDeriv ℝ (q - i) g x‖ ≤ |D (q - i)| :=
    (hD (q - i) (Nat.sub_le ..)).trans (le_abs_self _)
  calc
    (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (q - i) g x‖ ≤
        (q.choose i : ℝ) * (|A i| * t) * |D (q - i)| := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hAi (Nat.cast_nonneg _)
      · exact hDi
      · exact norm_nonneg _
      · positivity
    _ = (q.choose i : ℝ) * |A i| * |D (q - i)| * t := by ring

theorem norm_iteratedFDeriv_sum_le_const
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {ι : Type*} [Fintype ι] {f : ι → P → Q} {q : ℕ} {x : P}
    (hf : ∀ a, ContDiffAt ℝ q (f a) x) {L : ℝ}
    (h : ∀ a, ‖iteratedFDeriv ℝ q (f a) x‖ ≤ L) :
    ‖iteratedFDeriv ℝ q (fun y => ∑ a, f a y) x‖ ≤ Fintype.card ι * L := by
  classical
  rw [iteratedFDeriv_fun_sum_apply (fun a _ => hf a)]
  exact (norm_sum_le _ _).trans (by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun a _ => h a))

end Calculus

open ConnectionVariation Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

def radialCoframeCoeff
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (a : Fin n) (x u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  b.repr ((T x).inverse u) a

def radialConnectionCoeff
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (j a : Fin n) (x u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  b.repr (radialFrameConnection Γ T x u (b j)) a

theorem contDiff_radialCoframeCoeff
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (a : Fin n) (u : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun x => radialCoframeCoeff b T a x u) := by
  have hInv : ContDiff ℝ ∞ (fun x => (T x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hTi x).contDiffAt_map_inverse.comp x hT.contDiffAt
  simpa only [radialCoframeCoeff, OrthonormalBasis.repr_apply_apply,
    innerSL_apply_apply, Function.comp_def] using
    (innerSL ℝ (b a)).contDiff.comp (hInv.clm_apply contDiff_const)

theorem contDiff_radialConnectionCoeff
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hΓ : ContDiff ℝ ∞ Γ)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (j a : Fin n) (u : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun x => radialConnectionCoeff b Γ T j a x u) := by
  have h := (contDiff_radialFrameConnection_apply hΓ hT hTi).comp
    (contDiff_id.prodMk ((contDiff_const (c := u)).prodMk (contDiff_const (c := b j))))
  simpa only [radialConnectionCoeff, OrthonormalBasis.repr_apply_apply,
    innerSL_apply_apply, Function.comp_def, id_eq] using (innerSL ℝ (b a)).contDiff.comp h

theorem norm_iteratedFDeriv_radialCurvatureComponent_succ_le
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (l q : ℕ) (A B C C' : ℕ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hA : ∀ i ≤ q, ∀ a u,
      ‖iteratedFDeriv ℝ i (fun y => radialCoframeCoeff b T a y u) x‖ ≤ A i * ‖u‖)
    (hB : ∀ i ≤ q, ∀ j a u, ‖iteratedFDeriv ℝ i
      (fun y => radialConnectionCoeff b (christoffelBilinear g.euclideanCoefficients)
        T j a y u) x‖ ≤ B i * ‖u‖)
    (hC : ∀ i ≤ q, ∀ J : Fin (4 + l) → Fin n,
      ‖iteratedFDeriv ℝ i (radialCurvatureComponent D l (fun j => b (J j))) x‖ ≤ C i)
    (hC' : ∀ i ≤ q, ∀ J : Fin (4 + (l + 1)) → Fin n,
      ‖iteratedFDeriv ℝ i (radialCurvatureComponent D (l + 1) (fun j => b (J j))) x‖ ≤ C' i)
    (J : Fin (4 + l) → Fin n) :
    ‖iteratedFDeriv ℝ (q + 1) (radialCurvatureComponent D l (fun j => b (J j))) x‖ ≤
      curvatureComponentSuccJetBound n l q A B C C' := by
  classical
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  have hq : (q : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl q
  let K (s : ℕ) (Q : Fin (4 + s) → Fin n) :=
    radialCurvatureComponent D s (fun j => b (Q j))
  have hK (s : ℕ) (Q : Fin (4 + s) → Fin n) : ContDiff ℝ q (K s Q) :=
    (contDiff_radialCurvatureComponent D s _).of_le hq
  have hθ (a u) : ContDiff ℝ q (fun y => radialCoframeCoeff b T a y u) :=
    (contDiff_radialCoframeCoeff b hT hTi a u).of_le hq
  have hω (j a u) : ContDiff ℝ q (fun y => radialConnectionCoeff b Γ T j a y u) :=
    (contDiff_radialConnectionCoeff b hΓ hT hTi j a u).of_le hq
  apply norm_iteratedFDeriv_succ_le_of_directional isOpen_univ
    (contDiff_radialCurvatureComponent D l _).contDiffOn (mem_univ x) q
    (curvatureComponentSuccJetBound_nonneg ..)
  intro u
  let f₁ (a : Fin n) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
    radialCoframeCoeff b T a y u * K (l + 1) (Fin.cons a J) y
  let f₂ (j : Fin (4 + l)) (a : Fin n) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
    radialConnectionCoeff b Γ T (J j) a y u * K l (Function.update J j a) y
  have hf₁ (a) : ContDiff ℝ q (f₁ a) := (hθ a u).mul (hK _ _)
  have hf₂ (j a) : ContDiff ℝ q (f₂ j a) := (hω (J j) a u).mul (hK _ _)
  have h₁ (a) : ‖iteratedFDeriv ℝ q (f₁ a) x‖ ≤ scalarJetProductBound q A C' * ‖u‖ :=
    norm_iteratedFDeriv_mul_le_scaled_bound isOpen_univ (hθ a u).contDiffOn
      (hK _ _).contDiffOn (mem_univ x) A C' (norm_nonneg _)
      (fun i hi => hA i hi a u) (fun i hi => hC' i hi _)
  have h₂ (j a) : ‖iteratedFDeriv ℝ q (f₂ j a) x‖ ≤ scalarJetProductBound q B C * ‖u‖ :=
    norm_iteratedFDeriv_mul_le_scaled_bound isOpen_univ (hω (J j) a u).contDiffOn
      (hK _ _).contDiffOn (mem_univ x) B C (norm_nonneg _)
      (fun i hi => hB i hi (J j) a u) (fun i hi => hC i hi _)
  have hs₁ : ContDiffAt ℝ q (fun y => ∑ a, f₁ a y) x :=
    ContDiffAt.sum (fun a _ => (hf₁ a).contDiffAt)
  have hs₂ (j) : ContDiffAt ℝ q (fun y => ∑ a, f₂ j a y) x :=
    ContDiffAt.sum (fun a _ => (hf₂ j a).contDiffAt)
  have hsum₁ := norm_iteratedFDeriv_sum_le_const (fun a => (hf₁ a).contDiffAt) h₁
  have hsum₂ (j) := norm_iteratedFDeriv_sum_le_const (fun a => (hf₂ j a).contDiffAt) (h₂ j)
  have hsum₃ := norm_iteratedFDeriv_sum_le_const hs₂ hsum₂
  have heq : (fun y => fderiv ℝ (K l J) y u) =
      (fun y => (∑ a, f₁ a y) + ∑ j, ∑ a, f₂ j a y) := by
    funext y
    rw [fderiv_radialCurvatureComponent_eq_frame_sum D b hTi hTv]
    refine congrArg₂ (· + ·) ?_ ?_
    · rfl
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [f₂, K, radialConnectionCoeff]
      rw [radialFrameConnection_apply hT hTv]
      congr 2
      funext i
      by_cases hi : i = j <;> simp [hi]
  change ‖iteratedFDeriv ℝ q (fun y => fderiv ℝ (K l J) y u) x‖ ≤ _
  rw [heq, fun_iteratedFDeriv_add_apply hs₁ (ContDiffAt.sum (fun j _ => hs₂ j))]
  refine (norm_add_le _ _).trans ((add_le_add hsum₁ hsum₃).trans_eq ?_)
  simp only [Fintype.card_fin, curvatureComponentSuccJetBound]
  push_cast
  ring

end PoincareConjecture.CoordinateExponential
