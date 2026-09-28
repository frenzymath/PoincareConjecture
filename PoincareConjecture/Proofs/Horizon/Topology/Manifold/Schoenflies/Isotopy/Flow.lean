import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.CompactSupport
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private theorem exists_euclidean_diffeomorph_evolution
    {n : Nat} (W : Real × EuclideanSpace Real (Fin n) -> EuclideanSpace Real (Fin n))
    (hW : ContDiff Real ∞ W) {K : Set (EuclideanSpace Real (Fin n))}
    (hK : IsCompact K) (hzero : ∀ t x, x ∉ K -> W (t, x) = 0) :
    ∃ Φ : Real -> Real -> Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
      (∀ s x, Φ s s x = x) ∧
      (∀ s, ContDiff Real ∞ (fun z : Real × EuclideanSpace Real (Fin n) => Φ s z.1 z.2)) ∧
      (∀ s x t, HasDerivAt (fun r => Φ s r x) (W (t, Φ s t x)) t) ∧
      (∀ s t x, x ∉ K -> Φ s t x = x) := by
  let X : Real -> (x : EuclideanSpace Real (Fin n)) -> TangentSpace (𝓡 n) x :=
    fun t x => W (t, x)
  have hX : ContMDiff (𝓘(Real, Real).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : Real × EuclideanSpace Real (Fin n) =>
        (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 n) (EuclideanSpace Real (Fin n)))) := by
    intro z
    apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    have hw := hW.contDiffWithinAt (s := univ) (x := z)
    have hw' := hw.contMDiffWithinAt
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    convert hw' using 1 <;> first | rfl | simp [X]
  obtain ⟨E, hi, hs, ho, _, hinv⟩ :=
    Poincare.Manifold.exists_smooth_global_timeDependentFlow_of_compact_spatial_support
      isOpen_univ convex_univ hX.contMDiffOn
      (fun _ _ _ _ => ⟨K, hK, fun t _ x hx => hzero t x hx⟩)
  have hsmooth (s : Real) : ContDiff Real ∞
      (fun z : Real × EuclideanSpace Real (Fin n) => E s z.1 z.2) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using hs s (mem_univ s)
  let Φ (s t : Real) : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞ := {
    toEquiv := {
      toFun := E s t
      invFun := E t s
      left_inv := (hinv s (mem_univ _) t (mem_univ _)).1
      right_inv := (hinv s (mem_univ _) t (mem_univ _)).2 }
    contMDiff_toFun := ((hsmooth s).comp (contDiff_const.prodMk contDiff_id)).contMDiff
    contMDiff_invFun := ((hsmooth t).comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  refine ⟨Φ, fun s x => hi s (mem_univ _) x, hsmooth,
    fun s x t => ho s (mem_univ _) x t (mem_univ _), ?_⟩
  intro s t x hx
  have heq := Poincare.Manifold.timeDependent_integralCurve_eqOn isOpen_univ
    (convex_univ (𝕜 := Real)).isPreconnected (hX.of_le (by simp)).contMDiffOn
    (γ := fun r => E s r x) (η := fun _ => x)
    (fun r _ => (ho s (mem_univ _) x r (mem_univ _)).hasFDerivAt.hasMFDerivAt)
    (fun r _ => by
      change HasMFDerivAt _ _ (fun _ : Real => x) r
        ((1 : Real →L[Real] Real).smulRight (W (r, x)))
      rw [hzero r x hx]
      simpa using hasMFDerivAt_const (I := 𝓘(Real, Real)) (I' := 𝓡 n) x r)
    (mem_univ s) (hi s (mem_univ _) x)
  exact heq (mem_univ t)

theorem exists_diffeomorph_evolution_of_compact_spatial_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] (W : Real × E -> E)
    (hW : ContDiff Real ∞ W) {K : Set E} (hK : IsCompact K)
    (hzero : ∀ t x, x ∉ K -> W (t, x) = 0) :
    ∃ Φ : Real -> Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ s x, Φ s s x = x) ∧
      (∀ s, ContDiff Real ∞ (fun z : Real × E => Φ s z.1 z.2)) ∧
      (∀ s x t, HasDerivAt (fun r => Φ s r x) (W (t, Φ s t x)) t) ∧
      (∀ s t x, x ∉ K -> Φ s t x = x) := by
  let n := Module.finrank Real E
  let e : E ≃L[Real] EuclideanSpace Real (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let V : Real × EuclideanSpace Real (Fin n) -> EuclideanSpace Real (Fin n) :=
    fun z => e (W (z.1, e.symm z.2))
  have hV : ContDiff Real ∞ V :=
    e.contDiff.comp (hW.comp (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)))
  have hzeroV (t : Real) (x : EuclideanSpace Real (Fin n)) (hx : x ∉ e '' K) :
      V (t, x) = 0 := by
    have hpre : e.symm x ∉ K := fun h => hx ⟨e.symm x, h, e.apply_symm_apply x⟩
    simp only [V, hzero t (e.symm x) hpre, map_zero]
  obtain ⟨Ψ, hi, hs, ho, hfix⟩ :=
    exists_euclidean_diffeomorph_evolution V hV (hK.image e.continuous) hzeroV
  let Φ (s t : Real) : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toEquiv := e.toEquiv.trans ((Ψ s t).toEquiv.trans e.symm.toEquiv)
    contMDiff_toFun := e.symm.contDiff.contMDiff.comp
      ((Ψ s t).contMDiff.comp e.contDiff.contMDiff)
    contMDiff_invFun := e.symm.contDiff.contMDiff.comp
      ((Ψ s t).symm.contMDiff.comp e.contDiff.contMDiff) }
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro s x
    change e.symm (Ψ s s (e x)) = x
    rw [hi, e.symm_apply_apply]
  · intro s
    exact e.symm.contDiff.comp
      ((hs s).comp (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)))
  · intro s x t
    change HasDerivAt (fun r => e.symm (Ψ s r (e x)))
      (W (t, e.symm (Ψ s t (e x)))) t
    have h := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (ho s (e x) t)
    convert! h using 1
    simp [V]
  · intro s t x hx
    change e.symm (Ψ s t (e x)) = x
    rw [hfix s t (e x) (by simpa only [e.injective.mem_set_image] using hx),
      e.symm_apply_apply]

end Poincare.Manifold.Schoenflies
