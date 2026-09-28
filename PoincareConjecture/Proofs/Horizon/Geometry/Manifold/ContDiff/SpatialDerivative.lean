import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.LieBracket



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Filter Bundle

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma contMDiffAt_directional
    {f : M → ℝ} {X : (x : M) → TangentSpace I x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => mvfderiv I f y (X y)) x := by
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have h := hd.clm_apply_of_inCoordinates hX hf
  rw [contMDiffAt_totalSpace] at h
  convert h.2 using 1
  funext y
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  simp
  rfl



lemma contMDiffAt_mvfderiv_spatial
    {f : ℝ × M → ℝ} {t : ℝ} {x : M}
    {X : (y : M) → TangentSpace I y}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => mvfderiv I (fun y => f (p.1, y)) p.2 (X p.2)) (t, x) := by
  let V : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p := fun p => (0, X p.2)
  have hzero : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M => (⟨p.1, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) (t, x) := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_fst, ?_⟩
    simpa only [TangentBundle.trivializationAt_apply, mfld_simps, map_zero] using
      (contMDiffAt_const (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ))
        (n := ∞) (c := (0 : ℝ)) (x := (t, x)))
  have hV := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, ℝ)) (I' := I) (M := ℝ) (M' := M) (n := ∞)).contMDiffAt.comp
    (t, x) (hzero.prodMk (hX.comp (t, x) contMDiffAt_snd))
  have h := contMDiffAt_directional hf hV
  apply h.congr_of_eventuallyEq
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp
    (hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
  filter_upwards [hnear] with p hp
  have he := mfderiv_prod_eq_add_apply (hp.mdifferentiableAt (by simp))
    (v := V p)
  simp only [V, map_zero, zero_add] at he
  change mfderiv I 𝓘(ℝ, ℝ) (fun y => f (p.1, y)) p.2 (X p.2) =
    mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) f p (0, X p.2)
  exact he.symm

end Poincare.Manifold
