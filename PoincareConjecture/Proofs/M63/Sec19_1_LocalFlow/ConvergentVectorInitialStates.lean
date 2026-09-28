import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialCoordinateEncoder
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothSpectralInitialOrbit











set_option autoImplicit false

open AddCircle Filter PoincareConjecture.SpectralHeatNative
open scoped ContDiff Topology

namespace PoincareConjecture.M63





theorem exists_vectorPeriodic_initialStates_tendsto
    {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]
    (f f1 f2 : C(AddCircle L, ι → ℝ))
    (fn fn1 fn2 : ℕ → C(AddCircle L, ι → ℝ))
    (h1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L))
      (f1 (x : AddCircle L)) x)
    (h2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f1 (y : AddCircle L))
      (f2 (x : AddCircle L)) x)
    (hn1 : ∀ j (x : ℝ), HasDerivAt (fun y : ℝ => fn j (y : AddCircle L))
      (fn1 j (x : AddCircle L)) x)
    (hn2 : ∀ j (x : ℝ), HasDerivAt (fun y : ℝ => fn1 j (y : AddCircle L))
      (fn2 j (x : AddCircle L)) x)
    (hfn : Tendsto fn atTop (𝓝 f)) (hfn2 : Tendsto fn2 atTop (𝓝 f2)) :
    ∃ (w : State ((ℤ × Fin 2) × ι)) (wn : ℕ → State ((ℤ × Fin 2) × ι)),
      vectorPeriodicJet (L := L) 1 0 (by omega) w = f ∧
      (∀ j, vectorPeriodicJet (L := L) 1 0 (by omega) (wn j) = fn j) ∧
      Tendsto wn atTop (𝓝 w) ∧
      ∀ j, ContDiff ℝ ∞ (fun x : ℝ => fn j (x : AddCircle L)) →
        ContDiff ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (wn j)) := by
  classical
  let P (i : ι) : C(AddCircle L, ι → ℝ) →L[ℝ] C(AddCircle L, ℝ) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L)
  let A : (C(AddCircle L, ι → ℝ) × C(AddCircle L, ι → ℝ)) →L[ℝ]
      State ((ℤ × Fin 2) × ι) :=
    (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => realPeriodicH2Encode.comp ((P i).prodMap (P i))))
  have hAi (g h : C(AddCircle L, ι → ℝ)) (i : ι) :
      lpFinitePiEquiv ℝ (A (g, h)) i = realPeriodicH2Encode (P i g, P i h) := by
    change lpFinitePiEquiv ℝ ((lpFinitePiEquiv ℝ).symm
      (fun j => realPeriodicH2Encode (P j g, P j h))) i = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hencode (g g1 g2 : C(AddCircle L, ι → ℝ))
      (hg1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => g (y : AddCircle L))
        (g1 (x : AddCircle L)) x)
      (hg2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => g1 (y : AddCircle L))
        (g2 (x : AddCircle L)) x) :
      (∀ i (n : ℤ), complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (A (g, g2)) i) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L) (P i g)) n) ∧
      vectorPeriodicJet (L := L) 1 0 (by omega) (A (g, g2)) = g := by
    have hs (i : ι) := realPeriodicH2Encode_spec (P i g) (P i g1) (P i g2)
      (fun x => (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        x (hg1 x))
      (fun x => (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        x (hg2 x))
    refine ⟨?_, ?_⟩
    · intro i n
      rw [hAi]
      exact (hs i).1 n
    · ext x i
      change realPeriodicJet (L := L) 1 0 (by omega)
        (lpFinitePiEquiv ℝ (A (g, g2)) i) x = g x i
      rw [hAi, (hs i).2.1]
      rfl
  refine ⟨A (f, f2), fun j => A (fn j, fn2 j), (hencode f f1 f2 h1 h2).2,
    fun j => (hencode (fn j) (fn1 j) (fn2 j) (hn1 j) (hn2 j)).2,
    A.continuous.continuousAt.tendsto.comp (hfn.prodMk_nhds hfn2), ?_⟩
  intro j hj
  obtain ⟨v, hv, _hrec, _hbase, horbit⟩ :=
    exists_smooth_vectorPeriodic_spectral_initial_state (fn j) hj
  have heq : A (fn j, fn2 j) = v := by
    apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
    funext i
    apply complexLpRealEquiv.symm.injective
    apply lp.ext
    funext n
    exact ((hencode (fn j) (fn1 j) (fn2 j) (hn1 j) (hn2 j)).1 i n).trans (hv i n).symm
  change ContDiff ℝ ∞ (fun s : ℝ =>
    vectorPeriodicSpectralTranslation (L := L) s (A (fn j, fn2 j)))
  rw [heq]
  exact horbit

end PoincareConjecture.M63
