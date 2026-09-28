import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {J : Set ℝ}

private lemma differentiableWithinAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {S : Set ℝ} {t : ℝ}
    (hf : ∀ v, DifferentiableWithinAt ℝ (fun s => f s v) S t) :
    DifferentiableWithinAt ℝ f S t := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.differentiableAt.comp_differentiableWithinAt t
    (differentiableWithinAt_pi.mpr fun i => hf _)

private lemma hasDerivWithinAt_linear_moving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set ℝ} {t : ℝ}
    (ht : UniqueDiffWithinAt ℝ S t) (L : ℝ → E →L[ℝ] ℝ)
    (hL : ∀ a, DifferentiableWithinAt ℝ (fun s => L s a) S t)
    {v : ℝ → E} {v' : E} {d : ℝ}
    (hv : HasDerivWithinAt v v' S t)
    (hd : HasDerivWithinAt (fun s => L s (v t)) d S t) :
    HasDerivWithinAt (fun s => L s (v s)) (d + L t v') S t := by
  have h := (differentiableWithinAt_clm_of_apply hL).hasDerivWithinAt
  have hfixed := h.clm_apply (hasDerivWithinAt_const t S (v t))
  have he := hd.derivWithin ht
  have he' := hfixed.derivWithin ht
  have hval : d = (derivWithin L S t) (v t) := by
    calc
      d = derivWithin (fun s => L s (v t)) S t := he.symm
      _ = (derivWithin L S t) (v t) := by simpa only [map_zero, add_zero] using he'
  have hh := h.clm_apply hv
  simpa only [hval, add_comm] using hh

private lemma hasDerivWithinAt_four_moving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set ℝ} {t : ℝ}
    (ht : UniqueDiffWithinAt ℝ S t)
    (A : ℝ → MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (dA : (Fin 4 → E) → ℝ)
    (hA : ∀ q, HasDerivWithinAt (fun s => A s q) (dA q) S t)
    {u v w z : ℝ → E} {u' v' w' z' : E}
    (hu : HasDerivWithinAt u u' S t) (hv : HasDerivWithinAt v v' S t)
    (hw : HasDerivWithinAt w w' S t) (hz : HasDerivWithinAt z z' S t) :
    HasDerivWithinAt (fun s => A s ![u s, v s, w s, z s])
      (dA ![u t, v t, w t, z t] + A t ![u', v t, w t, z t] +
        A t ![u t, v', w t, z t] + A t ![u t, v t, w', z t] +
        A t ![u t, v t, w t, z']) S t := by
  classical
  let L (s : ℝ) (q : Fin 4 → E) (i : Fin 4) :=
    ((A s).toLinearMap q i).toContinuousLinearMap
  have hL (s : ℝ) (q : Fin 4 → E) (i : Fin 4) (a : E) :
      L s q i a = A s (Function.update q i a) := rfl
  have e0 (a b c d r : E) : Function.update ![a, b, c, d] 0 r = ![r, b, c, d] := by
    ext i; fin_cases i <;> simp
  have e1 (a b c d r : E) : Function.update ![a, b, c, d] 1 r = ![a, r, c, d] := by
    ext i; fin_cases i <;> simp
  have e2 (a b c d r : E) : Function.update ![a, b, c, d] 2 r = ![a, b, r, d] := by
    ext i; fin_cases i <;> simp
  have e3 (a b c d r : E) : Function.update ![a, b, c, d] 3 r = ![a, b, c, r] := by
    ext i; fin_cases i <;> simp
  have h1 (b c d : E) : HasDerivWithinAt (fun s => A s ![u s, b, c, d])
      (dA ![u t, b, c, d] + A t ![u', b, c, d]) S t := by
    simpa only [hL, e0] using hasDerivWithinAt_linear_moving ht
      (fun s => L s ![0, b, c, d] 0)
      (fun a => by simpa only [hL, e0] using (hA ![a, b, c, d]).differentiableWithinAt)
      hu (by simpa only [hL, e0] using hA ![u t, b, c, d])
  have h2 (c d : E) : HasDerivWithinAt (fun s => A s ![u s, v s, c, d])
      (dA ![u t, v t, c, d] + A t ![u', v t, c, d] +
        A t ![u t, v', c, d]) S t := by
    simpa only [hL, e1] using hasDerivWithinAt_linear_moving ht
      (fun s => L s ![u s, 0, c, d] 1)
      (fun b => by simpa only [hL, e1] using (h1 b c d).differentiableWithinAt)
      hv (by simpa only [hL, e1] using h1 (v t) c d)
  have h3 (d : E) : HasDerivWithinAt (fun s => A s ![u s, v s, w s, d])
      (dA ![u t, v t, w t, d] + A t ![u', v t, w t, d] +
        A t ![u t, v', w t, d] + A t ![u t, v t, w', d]) S t := by
    simpa only [hL, e2] using hasDerivWithinAt_linear_moving ht
      (fun s => L s ![u s, v s, 0, d] 2)
      (fun c => by simpa only [hL, e2] using (h2 c d).differentiableWithinAt)
      hw (by simpa only [hL, e2] using h2 (w t) d)
  simpa only [hL, e3] using hasDerivWithinAt_linear_moving ht
    (fun s => L s ![u s, v s, w s, 0] 3)
    (fun d => by simpa only [hL, e3] using (h3 d).differentiableWithinAt)
    hz (by simpa only [hL, e3] using h3 (z t))

noncomputable def ricciSharp (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) : TangentSpace (𝓡 n) x :=
  let b := g.orthonormalBasis x
  ∑ i, D.ricci x v (b i) • b i

private lemma curvatureReaction_add_ricciSharp
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureReaction x u v w z +
      D.curvatureTensor x (ricciSharp D x u) v w z +
      D.curvatureTensor x u (ricciSharp D x v) w z +
      D.curvatureTensor x u v (ricciSharp D x w) z +
      D.curvatureTensor x u v w (ricciSharp D x z) =
        2 * (D.curvatureB x u v w z - D.curvatureB x u v z w -
          D.curvatureB x u z v w + D.curvatureB x u w v z) := by
  classical
  obtain ⟨A, hA⟩ := hD.1.1 x
  have hslot (q : Fin 4 → TangentSpace (𝓡 n) x) (i : Fin 4) :
      D.riemannEvaluation x (Function.update q i (ricciSharp D x (q i))) =
        ∑ j, D.ricci x (q i) (g.orthonormalBasis x j) *
          D.riemannEvaluation x (Function.update q i (g.orthonormalBasis x j)) := by
    simp_rw [hA, ricciSharp, A.map_update_sum, A.map_update_smul, smul_eq_mul]
  have h0 := hslot ![u, v, w, z] 0
  have h1 := hslot ![u, v, w, z] 1
  have h2 := hslot ![u, v, w, z] 2
  have h3 := hslot ![u, v, w, z] 3
  simp [LeviCivitaData.riemannEvaluation, Function.update] at h0 h1 h2 h3
  rw [h0, h1, h2, h3, LeviCivitaData.curvatureReaction]
  simp only [Finset.sum_add_distrib]
  ring

theorem curvatureReaction_add_ricciSharp_eq
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureReaction x u v w z +
      D.curvatureTensor x (ricciSharp D x u) v w z +
      D.curvatureTensor x u (ricciSharp D x v) w z +
      D.curvatureTensor x u v (ricciSharp D x w) z +
      D.curvatureTensor x u v w (ricciSharp D x z) =
        2 * (D.curvatureB x u v w z - D.curvatureB x u v z w -
          D.curvatureB x u z v w + D.curvatureB x u w v z) := by
  exact curvatureReaction_add_ricciSharp D hD x u v w z

theorem hasDerivWithinAt_curvature_moving_inputs
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w z : ℝ → TangentSpace (𝓡 n) x)
    (hu : HasDerivWithinAt u (ricciSharp (F.connection t) x (u t)) J t)
    (hv : HasDerivWithinAt v (ricciSharp (F.connection t) x (v t)) J t)
    (hw : HasDerivWithinAt w (ricciSharp (F.connection t) x (w t)) J t)
    (hz : HasDerivWithinAt z (ricciSharp (F.connection t) x (z t)) J t) :
    HasDerivWithinAt
      (fun s => (F.connection s).curvatureTensor x (u s) (v s) (w s) (z s))
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![u t, v t, w t, z t] +
        2 * ((F.connection t).curvatureB x (u t) (v t) (w t) (z t) -
          (F.connection t).curvatureB x (u t) (v t) (z t) (w t) -
          (F.connection t).curvatureB x (u t) (z t) (v t) (w t) +
          (F.connection t).curvatureB x (u t) (w t) (v t) (z t))) J t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  choose A hA using fun s =>
    (hC.tensor_calculus n M (F.metric s) (F.connection s)).1.1 x
  let dA (q : Fin 4 → TangentSpace (𝓡 n) x) :=
    (F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
        ![q 0, q 1, q 2, q 3] +
      (F.connection t).curvatureReaction x (q 0) (q 1) (q 2) (q 3)
  have hfixed (q : Fin 4 → TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => A s q) (dA q) J t := by
    simpa only [← hA, LeviCivitaData.riemannEvaluation] using
      hC.curvature_evolution n M J F t (interior_subset ht) x (q 0) (q 1) (q 2) (q 3)
  have hmoving := hasDerivWithinAt_four_moving
    (uniqueDiffWithinAt_of_mem_nhds (mem_interior_iff_mem_nhds.mp ht))
    A dA hfixed hu hv hw hz
  simp [← hA, LeviCivitaData.riemannEvaluation, dA] at hmoving
  apply hmoving.congr_deriv
  have hcancel := curvatureReaction_add_ricciSharp (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (u t) (v t) (w t) (z t)
  linear_combination hcancel

end PoincareConjecture.RicciFlow
