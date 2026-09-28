import PoincareConjecture.Proofs.M09.CompactAdaptedField
import PoincareConjecture.Proofs.M09.AdaptedPairingConstancy
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_adapted_orthonormal_frame {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U) (hconnU : IsPreconnected U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (a c s0 : ℝ) (hKU : Set.Icc a c ⊆ U) (hs0 : s0 ∈ Set.Icc a c)
    (e : Fin n → TangentSpace (𝓡 n) (γ s0))
    (he : ∀ i j, (F.metric (T - s0 ^ 2)).inner (γ s0) (e i) (e j) =
      if i = j then 1 else 0) :
    ∃ (D : Set ℝ) (P : Fin n → ∀ t, TangentSpace (𝓡 n) (γ t)),
      IsOpen D ∧ IsPreconnected D ∧ Set.Icc a c ⊆ D ∧ D ⊆ U ∧
        (∀ i, P i s0 = e i) ∧ (∀ i, IsAdaptedFieldOn F T γ (P i) D) ∧
        ∀ t ∈ D, ∀ i j, (F.metric (T - t ^ 2)).inner (γ t) (P i t) (P j t) =
          if i = j then 1 else 0 := by
  classical
  choose D P hD hconn hKD hDU hP0 hP using fun i : Fin n ↦
    exists_adaptedFieldOn_Icc F T b hb hwindow γ U hU htime hγ a c s0 hKU hs0 (e i)
  let W := U ∩ ⋂ i, D i
  have hW : IsOpen W := hU.inter (isOpen_iInter_of_finite hD)
  have hconnW : IsPreconnected W :=
    (hconnU.ordConnected.inter (Set.ordConnected_iInter fun i ↦ (hconn i).ordConnected)).isPreconnected
  have hKW : Set.Icc a c ⊆ W := fun t ht ↦
    ⟨hKU ht, Set.mem_iInter.mpr (fun i ↦ hKD i ht)⟩
  have hWi (i : Fin n) : W ⊆ D i := fun _ ht ↦ Set.mem_iInter.mp ht.2 i
  have hPW (i : Fin n) := (hP i).mono (hWi i)
  refine ⟨W, P, hW, hconnW, hKW, Set.inter_subset_left, hP0, hPW, ?_⟩
  intro t ht i j
  have hp := IsAdaptedFieldOn.pairing_eq F T b hb hwindow γ (P i) (P j) W
    hW hconnW (fun _ h ↦ htime h.1) (hγ.mono Set.inter_subset_left)
    (hPW i) (hPW j) t s0 ht (hKW hs0)
  rw [hp, hP0 i, hP0 j]
  exact he i j

set_option backward.isDefEq.respectTransparency false in
theorem exists_orthonormalBasis_of_metric_pairing (g : RiemannianMetric n M) (p : M)
    (v : Fin n → TangentSpace (𝓡 n) p)
    (hv : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ e : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) p), ∀ i, e i = v i := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  have hon : Orthonormal ℝ v := orthonormal_iff_ite.mpr hv
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hsp := hon.linearIndependent.span_eq_top_of_card_eq_finrank'
    (by simpa only [Fintype.card_fin] using hdim.symm)
  refine ⟨OrthonormalBasis.mk hon hsp.ge, ?_⟩
  intro i
  exact congrFun (OrthonormalBasis.coe_mk hon hsp.ge) i

set_option backward.isDefEq.respectTransparency false in
theorem exists_initial_orthonormal_vectors (g : RiemannianMetric n M) (p : M) :
    ∃ e : Fin n → TangentSpace (𝓡 n) p,
      ∀ i j, g.inner p (e i) (e j) = if i = j then 1 else 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  let e := (g.orthonormalBasis p).reindex (finCongr hdim)
  exact ⟨e, orthonormal_iff_ite.mp e.orthonormal⟩

end PoincareConjecture.Proofs.M09
