import PoincareConjecture.Proofs.M09.ExponentialAdaptedFrame

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_orthonormal_vectors_containing_unit (g : RiemannianMetric n M) (p : M)
    (v : TangentSpace (𝓡 n) p) (hv : g.inner p v v = 1) :
    ∃ (e : Fin n → TangentSpace (𝓡 n) p) (i : Fin n), e i = v ∧
      ∀ j k, g.inner p (e j) (e k) = if j = k then 1 else 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hon : Orthonormal ℝ ((↑) : ({v} : Set (TangentSpace (𝓡 n) p)) → TangentSpace (𝓡 n) p) := by
    apply orthonormal_iff_ite.mpr
    intro x y
    have hx : (x : TangentSpace (𝓡 n) p) = v := Set.mem_singleton_iff.mp x.property
    have hy : (y : TangentSpace (𝓡 n) p) = v := Set.mem_singleton_iff.mp y.property
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    simp only [hxy, if_true, hx, hy]
    exact hv
  obtain ⟨S, b, hS, hb⟩ := hon.exists_orthonormalBasis_extension
  have hcard : Fintype.card S = n := by
    rw [← Module.finrank_eq_card_basis b.toBasis, hdim]
  let σ : S ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let e := b.reindex σ
  let j : S := ⟨v, hS (Set.mem_singleton v)⟩
  refine ⟨e, σ j, ?_, orthonormal_iff_ite.mp e.orthonormal⟩
  simp only [e, OrthonormalBasis.coe_reindex, Function.comp_apply, σ.symm_apply_apply, hb]
  rfl

theorem lExponentialFamily_exists_terminal_adapted_frame {J : Set ℝ} [T2Space M]
    {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (e : Fin n → TangentSpace (𝓡 n) (A.squareFamily Z (Real.sqrt b)))
    (he : ∀ i j, (F.metric (T - (Real.sqrt b) ^ 2)).inner (A.squareFamily Z (Real.sqrt b))
      (e i) (e j) = if i = j then 1 else 0) :
    ∃ (D : Set ℝ) (P : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s)),
      IsOpen D ∧ IsPreconnected D ∧ Set.Icc 0 (Real.sqrt b) ⊆ D ∧
        D ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ∧
        ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) D ∧
        (∀ i, P i (Real.sqrt b) = e i) ∧
        (∀ i, IsAdaptedFieldOn F T (A.squareFamily Z) (P i) D) ∧
        ∀ s ∈ D, ∀ i j, (F.metric (T - s ^ 2)).inner (A.squareFamily Z s)
          (P i s) (P j s) = if i = j then 1 else 0 := by
  obtain ⟨U, _, hU, hconn, hKU, htime, hα, _⟩ :=
    lExponentialFamily_exists_adapted_frame hτmax hwindow A Z b hb hmax
  obtain ⟨D, P, hD, hconnD, hKD, hDU, hPe, hP, hpair⟩ :=
    exists_adapted_orthonormal_frame F T τmax hτmax hwindow (A.squareFamily Z) U hU
      hconn htime hα 0 (Real.sqrt b) (Real.sqrt b) hKU ⟨Real.sqrt_nonneg b, le_rfl⟩ e he
  exact ⟨D, P, hD, hconnD, hKD, hDU.trans htime, hα.mono hDU, hPe, hP, hpair⟩

end PoincareConjecture.Proofs.M09
