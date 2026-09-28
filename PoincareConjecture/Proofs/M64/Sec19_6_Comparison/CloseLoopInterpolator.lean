import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorHorizontalColumn
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonCloseness











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in



theorem m64_vertical_column_eq_slice {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f p) :
    mfderiv (𝓡 2) (𝓡 3) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => f (annulusPoint (p 0) s)) (p 1) 1 := by
  have hline : HasDerivAt (annulusPoint (p 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) (p 1) := by
    have heq : annulusPoint (p 0) = fun s =>
        annulusPoint (p 0) 0 + s • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
      funext s
      ext i
      fin_cases i <;> simp [annulusPoint, EuclideanSpace.basisFun_apply]
    rw [heq]
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (p 1)).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 1)).const_add
        (annulusPoint (p 0) 0)
  have hp : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (annulusPoint (p 0)) (p 1) 1 =
      EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hline.deriv
  have hc := mfderiv_comp_apply_of_eq (p 1) hf
    hline.differentiableAt.mdifferentiableAt hp (1 : ℝ)
  rw [hd] at hc
  exact hc.symm




theorem m64_pair_interpolator_contMDiffAt
    (gamma beta : C1FreeLoopSpace (M := M))
    {H : ℝ × (M × M) → M} {p : LoopPlane}
    (hH : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 H
      (p 1, periodicFreeLoop gamma (p 0), periodicFreeLoop beta (p 0))) :
    ContMDiffAt (𝓡 2) (𝓡 3) 1
      (fun z : LoopPlane => H (z 1, periodicFreeLoop gamma (z 0),
        periodicFreeLoop beta (z 0))) p := by
  have hp0 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1 (fun z : LoopPlane => z 0) p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.contMDiff.contMDiffAt
  have hp1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1 (fun z : LoopPlane => z 1) p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.contMDiff.contMDiffAt
  exact hH.comp p (hp1.prodMk
    (((Proofs.M58.contMDiff_periodicFreeLoop gamma).contMDiffAt.comp p hp0).prodMk
      ((Proofs.M58.contMDiff_periodicFreeLoop beta).contMDiffAt.comp p hp0)))




theorem m64_pair_interpolator_column_bounds
    (g : RiemannianMetric 3 M) (gamma beta : C1FreeLoopSpace (M := M))
    {H : ℝ × (M × M) → M} {S B epsilon : ℝ}
    (hH : ∀ p ∈ m64AnnulusDomain,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 H
        (p 1, periodicFreeLoop gamma (p 0), periodicFreeLoop beta (p 0)))
    (hB : ∀ p ∈ m64AnnulusDomain,
      ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop gamma (p 0)),
        g.tangentNorm (periodicFreeLoop gamma (p 0)) v ≤ S →
      ∀ w : TangentSpace (𝓡 3) (periodicFreeLoop beta (p 0)),
        g.tangentNorm (periodicFreeLoop beta (p 0)) w ≤ S →
      g.tangentNorm (H (p 1, periodicFreeLoop gamma (p 0), periodicFreeLoop beta (p 0)))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) H
          (p 1, periodicFreeLoop gamma (p 0), periodicFreeLoop beta (p 0)) (0, v, w)) ≤ B)
    (hgamma : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (periodicFreeLoop gamma x) (curveVelocity (periodicFreeLoop gamma) x) ≤ S)
    (hbeta : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (periodicFreeLoop beta x) (curveVelocity (periodicFreeLoop beta) x) ≤ S)
    (hspeed : ∀ x : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (H (s, periodicFreeLoop gamma x, periodicFreeLoop beta x))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => H (t, periodicFreeLoop gamma x, periodicFreeLoop beta x)) s 1) =
        (g.edist (periodicFreeLoop gamma x) (periodicFreeLoop beta x)).toReal)
    (hshort : ∀ x : ℝ, g.edist (periodicFreeLoop gamma x) (periodicFreeLoop beta x) <
      ENNReal.ofReal epsilon)
    {p : LoopPlane} (hp : p ∈ m64AnnulusDomain) :
    let f : LoopPlane → M := fun z => H (z 1, periodicFreeLoop gamma (z 0),
      periodicFreeLoop beta (z 0))
    g.tangentNorm (f p) (mfderiv (𝓡 2) (𝓡 3) f p
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B ∧
    g.tangentNorm (f p) (mfderiv (𝓡 2) (𝓡 3) f p
      (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon := by
  dsimp only
  constructor
  · rw [m64_interpolator_horizontal_column_eq p
      ((Proofs.M58.contMDiff_periodicFreeLoop gamma).contMDiffAt.mdifferentiableAt one_ne_zero)
      ((Proofs.M58.contMDiff_periodicFreeLoop beta).contMDiffAt.mdifferentiableAt one_ne_zero)
      ((hH p hp).mdifferentiableAt one_ne_zero)]
    exact hB p hp _ (hgamma (p 0) ⟨hp.1, hp.2.1⟩) _ (hbeta (p 0) ⟨hp.1, hp.2.1⟩)
  · rw [m64_vertical_column_eq_slice
      ((m64_pair_interpolator_contMDiffAt gamma beta (hH p hp)).mdifferentiableAt one_ne_zero)]
    simp only [annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hspeed (p 0) (p 1) ⟨hp.2.2.1, hp.2.2.2⟩]
    exact (ENNReal.toReal_lt_of_lt_ofReal (hshort (p 0))).le

end PoincareConjecture
