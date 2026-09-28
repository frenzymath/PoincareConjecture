import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Flow.ParametricComplete
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Plane.HorizontalEscape
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.UniqueScalarRoot
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold.PlaneDiffeomorph

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "v₀" => (!₂[(1 : ℝ), 0] : E₂)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

private theorem contDiff_pair
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (!₂[f x, g x] : E₂)) := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hg



theorem exists_smooth_horizontal_section_time
    {H : P × E₂ → E₂} (hH : ContDiff ℝ ∞ H) (hne : ∀ p x, H (p, x) ≠ 0)
    {L R B T : ℝ}
    (hfix : ∀ p x, x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → H (p, x) = v₀)
    (c : ℝ) (hc : c ≤ L ∨ R ≤ c)
    {Φ : P → ℝ → E₂ → E₂}
    (hΦ : ContDiff ℝ ∞ (fun z : P × (ℝ × E₂) => Φ z.1 z.2.1 z.2.2))
    (hflow : ∀ p x t, HasDerivAt (fun s => Φ p s x) (H (p, Φ p t x)) t) :
    ∃ τ : P × E₂ → ℝ, ContDiff ℝ ∞ τ ∧
      (∀ p x, Φ p (τ (p, x)) x 0 = c) ∧
      ∀ p x t, Φ p t x 0 = c → t = τ (p, x) := by
  have hex (q : P × E₂) : ∃! t : ℝ, Φ q.1 t q.2 0 = c :=
    Poincare.ODE.Plane.existsUnique_exterior_horizontal_section_hit
      (hH.comp (contDiff_const.prodMk contDiff_id)) (hne q.1) (hfix q.1) hc (hflow q.1 q.2)
  choose τ hτ hτunique using hex
  refine ⟨τ, ?_, fun p x => hτ (p, x), fun p x t => hτunique (p, x) t⟩
  let f : (P × E₂) × ℝ → ℝ := fun z => Φ z.1.1 z.2 z.1.2 0
  have hf : ContDiff ℝ ∞ f := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp (hΦ.comp
    ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))))
  apply Poincare.Analysis.contDiff_unique_scalar_root hf isOpen_univ
    (fun _ => mem_univ _) hτ (d := fun _ => 1) _ (by simp) (fun q t _ => hτunique q t)
  intro q
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt
    (τ q) (hflow q.1 q.2 (τ q))
  have hfixed : H (q.1, Φ q.1 (τ q) q.2) = v₀ := by
    apply hfix
    rcases hc with hc | hc
    · exact Or.inl ((hτ q).le.trans hc)
    · exact Or.inr (Or.inl (hc.trans (hτ q).ge))
  simpa only [EuclideanSpace.coe_proj, Function.comp_def,
    hfixed, Matrix.cons_val_zero] using hd



theorem exists_horizontal_flow_coordinates
    {H : P × E₂ → E₂} (hH : ContDiff ℝ ∞ H) (hne : ∀ p x, H (p, x) ≠ 0)
    {L R B T : ℝ}
    (hfix : ∀ p x, x 0 ≤ L ∨ R ≤ x 0 ∨ x 1 ≤ B ∨ T ≤ x 1 → H (p, x) = v₀)
    {Φ : P → ℝ → E₂ → E₂}
    (hΦ : ContDiff ℝ ∞ (fun z : P × (ℝ × E₂) => Φ z.1 z.2.1 z.2.2))
    (hinit : ∀ p x, Φ p 0 x = x)
    (hflow : ∀ p x t, HasDerivAt (fun s => Φ p s x) (H (p, Φ p t x)) t)
    (hcomp : ∀ p s t x, Φ p (s + t) x = Φ p s (Φ p t x)) :
    ∃ D : P → Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞,
      ContDiff ℝ ∞ (fun z : P × E₂ => D z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : P × E₂ => (D z.1).symm z.2) ∧
      ∀ p x, D p x = Φ p (x 0 - L) (!₂[L, x 1]) := by
  obtain ⟨τ, hτsmooth, hτ, hτunique⟩ :=
    exists_smooth_horizontal_section_time hH hne hfix L (Or.inl le_rfl) hΦ hflow
  let A : P × E₂ → E₂ := fun z => Φ z.1 (z.2 0 - L) (!₂[L, z.2 1])
  let C : P × E₂ → E₂ := fun z => Φ z.1 (τ z) z.2
  let Bmap : P × E₂ → E₂ := fun z => !₂[L - τ z, C z 1]
  have hA : ContDiff ℝ ∞ A := hΦ.comp (contDiff_fst.prodMk
    ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_snd).sub contDiff_const).prodMk
      (contDiff_pair contDiff_const
        ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_snd))))
  have hC : ContDiff ℝ ∞ C := hΦ.comp
    (contDiff_fst.prodMk (hτsmooth.prodMk contDiff_snd))
  have hB : ContDiff ℝ ∞ Bmap := contDiff_pair (contDiff_const.sub hτsmooth)
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hC)
  have hinv (p : P) (t : ℝ) (x : E₂) : Φ p (-t) (Φ p t x) = x := by
    rw [← hcomp, neg_add_cancel, hinit]
  have hleft (p : P) (x : E₂) : Bmap (p, A (p, x)) = x := by
    have htime : τ (p, A (p, x)) = -(x 0 - L) := by
      symm
      apply hτunique
      simp only [A, hinv, Matrix.cons_val_zero]
    have hback : C (p, A (p, x)) = !₂[L, x 1] := by
      simp only [C, htime, A, hinv]
    ext i
    fin_cases i
    · simp [Bmap, htime]
    · simp [Bmap, hback]
  have hright (p : P) (x : E₂) : A (p, Bmap (p, x)) = x := by
    have hstart : (!₂[L, C (p, x) 1] : E₂) = C (p, x) := by
      ext i
      fin_cases i
      · exact (hτ p x).symm
      · rfl
    change Φ p ((L - τ (p, x)) - L) (!₂[L, C (p, x) 1]) = x
    rw [show (L - τ (p, x)) - L = -τ (p, x) by ring, hstart]
    exact hinv p (τ (p, x)) x
  let D (p : P) : Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞ := {
    toEquiv := {
      toFun := fun x => A (p, x)
      invFun := fun x => Bmap (p, x)
      left_inv := hleft p
      right_inv := hright p }
    contMDiff_toFun := (hA.comp (contDiff_const.prodMk contDiff_id)).contMDiff
    contMDiff_invFun := (hB.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  exact ⟨D, hA, hB, fun _ _ => rfl⟩

end Poincare.Manifold.PlaneDiffeomorph
