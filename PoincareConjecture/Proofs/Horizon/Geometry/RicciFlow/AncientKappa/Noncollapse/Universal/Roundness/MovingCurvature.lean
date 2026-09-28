import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.GeometricPreservation.Transport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.AncientKappaRoundness

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
  simpa only [hval, add_comm] using h.clm_apply hv

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
      (dA ![u t, v t, c, d] + A t ![u', v t, c, d] + A t ![u t, v', c, d]) S t := by
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

end PoincareConjecture.AncientKappaRoundness

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem canonicalTransport_hasDerivAt_curvature_of_applied
    (F : RicciFlow n M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : M,
      ∀ u v w z : TangentSpace (𝓡 n) x,
      HasDerivWithinAt (fun s => (F.connection s).curvatureTensor x u v w z)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
          (F.connection t).curvatureReaction x u v w z) (Ico a b) t)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt
      (fun s => (F.connection s).curvatureTensor x
        (canonicalTransport F s x u) (canonicalTransport F s x v)
        (canonicalTransport F s x w) (canonicalTransport F s x z))
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![canonicalTransport F t x u, canonicalTransport F t x v,
            canonicalTransport F t x w, canonicalTransport F t x z] +
        2 * ((F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x v)
            (canonicalTransport F t x w) (canonicalTransport F t x z) -
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x v)
            (canonicalTransport F t x z) (canonicalTransport F t x w) -
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x z)
            (canonicalTransport F t x v) (canonicalTransport F t x w) +
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x w)
            (canonicalTransport F t x v) (canonicalTransport F t x z))) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  choose A hA using fun s => (hcalculus s).1.1 x
  let dA (q : Fin 4 → TangentSpace (𝓡 n) x) :=
    (F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
        ![q 0, q 1, q 2, q 3] +
      (F.connection t).curvatureReaction x (q 0) (q 1) (q 2) (q 3)
  have hfixed (q : Fin 4 → TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => A s q) (dA q) (Ico a b) t := by
    simpa only [← hA, LeviCivitaData.riemannEvaluation] using
      hevolution t ⟨ht.1.le, ht.2⟩ x (q 0) (q 1) (q 2) (q 3)
  have hinput (q : TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => canonicalTransport F s x q)
        (ricciSharp (F.connection t) x (canonicalTransport F t x q)) (Ico a b) t := by
    have h := (canonicalTransport_hasDerivWithinAt F ⟨ht.1.le, ht.2⟩ x).clm_apply
      (hasDerivWithinAt_const t (Ico a b) q)
    simpa only [map_zero, add_zero, ContinuousLinearMap.comp_apply,
      ricciEndomorphism_eq_sum F x ⟨ht.1.le, ht.2⟩, ricciSharp] using h
  have hn : Ico a b ∈ 𝓝 t := Ico_mem_nhds ht.1 ht.2
  have hmoving := AncientKappaRoundness.hasDerivWithinAt_four_moving
    (uniqueDiffWithinAt_of_mem_nhds hn) A dA hfixed
    (hinput u) (hinput v) (hinput w) (hinput z)
  simp [← hA, LeviCivitaData.riemannEvaluation, dA] at hmoving
  apply (hmoving.hasDerivAt hn).congr_deriv
  have hcancel := curvatureReaction_add_ricciSharp_eq (F.connection t) (hcalculus t) x
    (canonicalTransport F t x u) (canonicalTransport F t x v)
    (canonicalTransport F t x w) (canonicalTransport F t x z)
  linear_combination hcancel

end PoincareConjecture.RicciFlow.Frame
