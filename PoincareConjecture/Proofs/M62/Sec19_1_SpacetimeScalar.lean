import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62.SpacetimeCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem mvfderiv_product_scalar (C : SpacetimeCharts n M a b)
    (f : M × ℝ → ℝ) (q : C.Point)
    (hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      f (q.1, (q.2 : ℝ)))
    (V : TangentSpace (𝓡 (n + 1)) q) :
    mvfderiv (𝓡 (n + 1)) (fun r : C.Point => f (r.1, (r.2 : ℝ))) q V =
      mvfderiv (𝓡 n) (fun p => f (p, (q.2 : ℝ))) q.1 (C.split q V).1 +
        (C.split q V).2 * deriv (fun t => f (q.1, t)) q.2 := by
  let := C.chartedSpace
  have hs := C.contMDiff_space.mdifferentiableAt (x := q) (by simp)
  have ht := C.contMDiff_clock.mdifferentiableAt (x := q) (by simp)
  have hchain := mfderiv_comp_apply
    (f := fun r : C.Point => (r.1, (r.2 : ℝ))) (g := f)
    q hf (hs.prodMk ht) V
  rw [mfderiv_prodMk hs ht] at hchain
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
    (v := ((C.split q V).1, (C.split q V).2)) hf
  have htime : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t => f (q.1, t)) (q.2 : ℝ) (C.split q V).2 =
        (C.split q V).2 * deriv (fun t => f (q.1, t)) q.2 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun t => f (q.1, t)) (q.2 : ℝ) (C.split q V).2 = _
    simpa only [smul_eq_mul] using
      (fderiv_eq_smul_deriv (𝕜 := ℝ) (f := fun t => f (q.1, t))
        (x := (q.2 : ℝ)) (C.split q V).2)
  rw [htime] at hsplit
  change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ)
      (fun r : C.Point => f (r.1, (r.2 : ℝ))) q V =
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) f (q.1, (q.2 : ℝ))
      (mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst : C.Point → M) q V,
        mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (fun r : C.Point => (r.2 : ℝ)) q V) at hchain
  rw [← C.split_space, ← C.split_time] at hchain
  exact hchain.trans hsplit

theorem mvfderiv_product_horizontal (C : SpacetimeCharts n M a b)
    (f : M × ℝ → ℝ) (q : C.Point)
    (hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      f (q.1, (q.2 : ℝ)))
    (V : TangentSpace (𝓡 n) q.1) :
    mvfderiv (𝓡 (n + 1)) (fun r : C.Point => f (r.1, (r.2 : ℝ))) q
        (C.horizontal q V) =
      mvfderiv (𝓡 n) (fun p => f (p, (q.2 : ℝ))) q.1 V := by
  rw [C.mvfderiv_product_scalar f q hf]
  simp [horizontal]

theorem mvfderiv_product_time (C : SpacetimeCharts n M a b)
    (f : M × ℝ → ℝ) (q : C.Point)
    (hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      f (q.1, (q.2 : ℝ))) :
    mvfderiv (𝓡 (n + 1)) (fun r : C.Point => f (r.1, (r.2 : ℝ))) q
        (C.timeVector q) = deriv (fun t => f (q.1, t)) q.2 := by
  rw [C.mvfderiv_product_scalar f q hf]
  simp [timeVector]

end PoincareConjecture.M62.SpacetimeCharts
