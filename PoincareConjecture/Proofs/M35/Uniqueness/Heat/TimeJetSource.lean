import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffWeakEquation
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.HigherLowerOrder
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeOperatorJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem cutoff_value_pairing (K : Set V) (χ : 𝓢(V, ℝ)) (hχK : tsupport χ ⊆ K)
    (U : dirichletValue K) (φ : 𝓢(V, ℝ)) :
    inner ℝ (dirichletInclusion K (intoDirichletForm K (cutoffSupportedTest K χ hχK φ))) U =
      inner ℝ (schwartzMultiplier χ (U : L2)) (φ.toLp 2 volume) := by
  change inner ℝ ((schwartzProduct χ φ).toLp 2 volume) (U : L2) = _
  rw [schwartzProduct_toLp, schwartzMultiplier_selfAdjoint, real_inner_comm]

theorem exists_timeJet_cutoff_source {K : Set V} (hK : IsClosed K)
    (A : ℕ → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℕ → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℕ → Fin m → Fin m → 𝓢(V, ℝ))
    (u : ℕ → PiLp 2 (fun _ : Fin m => dirichletForm K))
    (l s : ℕ)
    (hbase : ∀ j k, HasInteriorWeakJets K (u j k) (s + 1))
    (hlower : ∀ j < l, ∀ k, HasInteriorWeakJets K (u j k) (s + 2))
    (heq : ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (u (l + 1))) =
      ∑ p ∈ Finset.antidiagonal l, (l.choose p.1 : ℝ) *
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (dirichletVectorLowerOrder hK (B p.1) (C p.1) (u p.2)) -
            principalVectorEnergy K (A p.1) z (u p.2)))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin m) :
    ∃ G : L2, HasFiniteWeakJet G s ∧ ∀ φ : 𝓢(V, ℝ),
      principalEnergy K (A 0) (intoDirichletForm K
        (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) (u l k) =
          inner ℝ G (φ.toLp 2 volume) := by
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
  have hprincipal (p : {p : ℕ × ℕ // p ∈ T}) : ∃ G : L2,
      HasFiniteWeakJet G s ∧ ∀ φ : 𝓢(V, ℝ),
        principalEnergy K (A p.1.1) (intoDirichletForm K
          (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) (u p.1.2 k) =
            inner ℝ G (φ.toLp 2 volume) :=
    exists_cutoff_principal_source K (A p.1.1) χ hχ hχK (u p.1.2 k)
      (hlower p.1.2 (hlt p.2) k)
  choose GP hGP hGPeq using hprincipal
  let lowSource : ℕ × ℕ → L2 := fun p => schwartzMultiplier χ
    (dirichletVectorLowerOrder hK (B p.1) (C p.1) (u p.2) k : L2)
  have hGL (p : ℕ × ℕ) : HasFiniteWeakJet (lowSource p) s :=
    hasFiniteWeakJet_localized_vector_lowerOrder hK (B p.1) (C p.1) (u p.2)
      (hbase p.2) χ hχ hχK k
  let GT : L2 := localizedDirichletValue K χ (u (l + 1) k)
  have hGT : HasFiniteWeakJet GT s :=
    (hbase (l + 1) k χ hχ hχK).mono (Nat.le_succ s)
  let term : {p : ℕ × ℕ // p ∈ T} → L2 := fun p =>
    l.choose p.1.1 • (lowSource p.1 - GP p)
  refine ⟨lowSource (0, l) - GT + ∑ p, term p,
    ((hGL (0, l)).sub hGT).add (HasFiniteWeakJet.sum _
      (fun p => ((hGL p.1).sub (hGP p)).nsmul _)), ?_⟩
  intro φ
  let v := intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)
  let z : PiLp 2 (fun _ : Fin m => dirichletForm K) := finiteHilbertSingle k v
  have he := heq z
  have hI (W : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) W =
        inner ℝ (schwartzMultiplier χ (W k : L2)) (φ.toLp 2 volume) :=
    (inner_finiteHilbertMap_single (dirichletInclusion K) k v W).trans
      (cutoff_value_pairing K χ (hχK.trans interior_subset) (W k) φ)
  have hP (j q : ℕ) : principalVectorEnergy K (A j) z (u q) =
      principalEnergy K (A j) v (u q k) := principalVectorEnergy_single_left K (A j) k v (u q)
  have htime : inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
      (finiteHilbertMap (dirichletInclusion K) (u (l + 1))) = inner ℝ GT (φ.toLp 2 volume) := by
    simpa only [GT, localizedDirichletValue, finiteHilbertMap_apply] using
      hI (finiteHilbertMap (dirichletInclusion K) (u (l + 1)))
  let f : ℕ × ℕ → ℝ := fun p => (l.choose p.1 : ℝ) *
    (inner ℝ (lowSource p) (φ.toLp 2 volume) - principalEnergy K (A p.1) v (u p.2 k))
  have he' : inner ℝ GT (φ.toLp 2 volume) = ∑ p ∈ Finset.antidiagonal l, f p := by
    simpa only [htime, hI, hP, lowSource, f] using he
  have hzero : f (0, l) = inner ℝ (lowSource (0, l)) (φ.toLp 2 volume) -
      principalEnergy K (A 0) v (u l k) := by simp only [f, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  have hsum : (∑ p : {p : ℕ × ℕ // p ∈ T}, inner ℝ (term p) (φ.toLp 2 volume)) =
      ∑ p ∈ T, f p := by
    rw [← Finset.sum_attach T]
    apply Finset.sum_congr rfl
    intro p _
    simp only [term, inner_smul_left_eq_smul, inner_sub_left, nsmul_eq_mul, f, v, hGPeq p φ]
  have hsplit := Finset.sum_erase_add (Finset.antidiagonal l) f
    (by simp : (0, l) ∈ Finset.antidiagonal l)
  change (∑ p ∈ T, f p) + f (0, l) = _ at hsplit
  rw [hzero] at hsplit
  simp only [inner_add_left, inner_sub_left, sum_inner, hsum]
  linarith only [he', hsplit]

end PoincareConjecture.M35.Uniqueness.Heat
