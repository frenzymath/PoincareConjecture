import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousLowerSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousPrincipalSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeJetSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n m : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_continuous_timeJet_cutoff_source {K : Set V} (hK : IsClosed K)
    (A : ℕ → ι → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℕ → ι → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℕ → ι → Fin m → Fin m → 𝓢(V, ℝ))
    (u : ℕ → ι → PiLp 2 (fun _ : Fin m => dirichletForm K)) (l s : ℕ)
    (hA : ∀ r i j w, w.length ≤ s + 1 →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A r t i j))))
    (hB : ∀ r i j k w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (B r t i j k))))
    (hC : ∀ r i j w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (C r t i j))))
    (hbase : ∀ j k, HasContinuousInteriorJets K (fun t => u j t k) (s + 1))
    (hlower : ∀ j < l, ∀ k, HasContinuousInteriorJets K (fun t => u j t k) (s + 2))
    (heq : ∀ t, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (u (l + 1) t)) =
      ∑ p ∈ Finset.antidiagonal l, (l.choose p.1 : ℝ) *
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (dirichletVectorLowerOrder hK (B p.1 t) (C p.1 t) (u p.2 t)) -
            principalVectorEnergy K (A p.1 t) z (u p.2 t)))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin m) :
    ∃ G : ι → L2, HasContinuousWeakJet G s ∧ ∀ t (φ : 𝓢(V, ℝ)),
      principalEnergy K (A 0 t) (intoDirichletForm K
        (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) (u l t k) =
          inner ℝ (G t) (φ.toLp 2 volume) := by
  classical
  let T := (Finset.antidiagonal l).erase (0, l)
  have hlt {p : ℕ × ℕ} (hp : p ∈ T) : p.2 < l := by
    have hp' := Finset.mem_erase.mp hp
    have hsum := Finset.mem_antidiagonal.mp hp'.2
    have hne : p ≠ (0, l) := hp'.1
    by_contra h
    have h2 : p.2 = l := by omega
    have h1 : p.1 = 0 := by omega
    exact hne (Prod.ext h1 h2)
  have hprincipal (p : {p : ℕ × ℕ // p ∈ T}) : ∃ G : ι → L2,
      HasContinuousWeakJet G s ∧ ∀ t (φ : 𝓢(V, ℝ)),
        principalEnergy K (A p.1.1 t) (intoDirichletForm K
          (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) (u p.1.2 t k) =
            inner ℝ (G t) (φ.toLp 2 volume) :=
    exists_continuous_cutoff_principal_source K (A p.1.1) (hA p.1.1) χ hχ hχK
      (fun t => u p.1.2 t k) (hlower p.1.2 (hlt p.2) k)
  choose GP hGP hGPeq using hprincipal
  let lowSource : ℕ × ℕ → ι → L2 := fun p t => schwartzMultiplier χ
    (dirichletVectorLowerOrder hK (B p.1 t) (C p.1 t) (u p.2 t) k : L2)
  have hGL (p : ℕ × ℕ) : HasContinuousWeakJet (lowSource p) s :=
    hasContinuousWeakJet_localized_vector_lowerOrder hK (B p.1) (C p.1) (hB p.1) (hC p.1)
      (u p.2) (hbase p.2) χ hχ hχK k
  let GT : ι → L2 := fun t => localizedDirichletValue K χ (u (l + 1) t k)
  have hGT : HasContinuousWeakJet GT s :=
    (hbase (l + 1) k χ hχ hχK).mono (Nat.le_succ s)
  let term : {p : ℕ × ℕ // p ∈ T} → ι → L2 := fun p t =>
    l.choose p.1.1 • (lowSource p.1 t - GP p t)
  refine ⟨fun t => lowSource (0, l) t - GT t + ∑ p, term p t,
    ((hGL (0, l)).sub hGT).add (HasContinuousWeakJet.sum _
      (fun p => ((hGL p.1).sub (hGP p)).nsmul _)), ?_⟩
  intro t φ
  let v := intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)
  let z : PiLp 2 (fun _ : Fin m => dirichletForm K) := finiteHilbertSingle k v
  have he := heq t z
  have hI (W : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) W =
        inner ℝ (schwartzMultiplier χ (W k : L2)) (φ.toLp 2 volume) :=
    (inner_finiteHilbertMap_single (dirichletInclusion K) k v W).trans
      (cutoff_value_pairing K χ (hχK.trans interior_subset) (W k) φ)
  have hP (j q : ℕ) : principalVectorEnergy K (A j t) z (u q t) =
      principalEnergy K (A j t) v (u q t k) :=
    principalVectorEnergy_single_left K (A j t) k v (u q t)
  have htime : inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
      (finiteHilbertMap (dirichletInclusion K) (u (l + 1) t)) =
        inner ℝ (GT t) (φ.toLp 2 volume) := by
    simpa only [GT, localizedDirichletValue, finiteHilbertMap_apply] using
      hI (finiteHilbertMap (dirichletInclusion K) (u (l + 1) t))
  let f : ℕ × ℕ → ℝ := fun p => (l.choose p.1 : ℝ) *
    (inner ℝ (lowSource p t) (φ.toLp 2 volume) - principalEnergy K (A p.1 t) v (u p.2 t k))
  have he' : inner ℝ (GT t) (φ.toLp 2 volume) = ∑ p ∈ Finset.antidiagonal l, f p := by
    simpa only [htime, hI, hP, lowSource, f] using he
  have hzero : f (0, l) = inner ℝ (lowSource (0, l) t) (φ.toLp 2 volume) -
      principalEnergy K (A 0 t) v (u l t k) := by
    simp only [f, Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hsum : (∑ p : {p : ℕ × ℕ // p ∈ T}, inner ℝ (term p t) (φ.toLp 2 volume)) =
      ∑ p ∈ T, f p := by
    rw [← Finset.sum_attach T]
    apply Finset.sum_congr rfl
    intro p _
    simp only [term, inner_smul_left_eq_smul, inner_sub_left, nsmul_eq_mul, f, v, hGPeq p t φ]
  have hsplit := Finset.sum_erase_add (Finset.antidiagonal l) f
    (by simp : (0, l) ∈ Finset.antidiagonal l)
  change (∑ p ∈ T, f p) + f (0, l) = _ at hsplit
  rw [hzero] at hsplit
  simp only [inner_add_left, inner_sub_left, sum_inner, hsum]
  linarith only [he', hsplit]

end PoincareConjecture.M35.Uniqueness.Heat
