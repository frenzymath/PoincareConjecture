import PoincareConjecture.Proofs.M30.Thm11_1.TerminalRicciKernel
import PoincareConjecture.Proofs.M30.Thm11_1.FiniteParallelSection
import PoincareConjecture.Proofs.M30.Thm11_1.NullityTransport












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u v w

namespace PoincareConjecture.M30





theorem terminal_nullity_and_local_parallel_sections
    {ι : Type w} {N : ι → Type u} {M : Type v}
    [∀ i, TopologicalSpace (N i)] [TopologicalSpace M]
    [∀ i, T2Space (N i)] [∀ i, ConnectedSpace (N i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [∀ i, IsManifold (𝓡 3) ∞ (N i)] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u})
    (a : ι → ℝ) (ha : ∀ i, a i < 0)
    (F : ∀ i, RicciFlow 3 (N i) (Icc (a i) 0))
    (hoperator : ∀ i, ∀ t ∈ Icc (a i) 0, ∀ z : N i,
      ((F i).connection t).NonnegativeCurvatureOperator z)
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (e : ∀ i, N i → M)
    (he : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i))
    (hmetric : ∀ i, ∀ z : N i, ∀ v1 v2 : TangentSpace (𝓡 3) z,
      ((F i).metric 0).inner z v1 v2 = g.inner (e i z)
        (mfderiv (𝓡 3) (𝓡 3) (e i) z v1)
        (mfderiv (𝓡 3) (𝓡 3) (e i) z v2))
    (p0 : M) (hnonflat : D.curvatureTensorNorm p0 ≠ 0)
    (x : M) (v1 v2 : TangentSpace (𝓡 3) x)
    (hv1 : g.inner x v1 v1 = 1) (hv2 : g.inner x v2 v2 = 1)
    (horth : g.inner x v1 v2 = 0)
    (hzero : D.curvatureTensor x v1 v2 v1 v2 = 0)
    (hcapture : ∀ y : M, ∃ i : ι,
      x ∈ range (e i) ∧ p0 ∈ range (e i) ∧ y ∈ range (e i)) :
    (∀ y : M, ricciNullity D y = 1) ∧
      ∀ p : UnitRicciKernel D,
        ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 3) y),
          IsOpen U ∧ p.1.proj ∈ U ∧
          ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
          V p.1.proj = p.1.snd ∧
          ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
            (∀ z : TangentSpace (𝓡 3) y, D.ricci y (V y) z = 0) ∧
            ∀ z : TangentSpace (𝓡 3) y, D.connection V y z = 0 := by
  classical
  have hterminal : ∀ i : ι, x ∈ range (e i) → p0 ∈ range (e i) →
      ∀ y : N i, ricciNullity ((F i).connection 0) y = 1 := by
    intro i hxi hp0
    obtain ⟨xi, hxi⟩ := hxi
    obtain ⟨pi, hpi⟩ := hp0
    subst x
    subst p0
    let L := mfderiv (𝓡 3) (𝓡 3) (e i) xi
    have hL : L.IsInvertible :=
      ⟨(he i xi).mfderivToContinuousLinearEquiv (by simp), rfl⟩
    let u1 : TangentSpace (𝓡 3) xi := L.inverse v1
    let u2 : TangentSpace (𝓡 3) xi := L.inverse v2
    have hu1 : L u1 = v1 := hL.self_apply_inverse v1
    have hu2 : L u2 = v2 := hL.self_apply_inverse v2
    have hu1norm : ((F i).metric 0).inner xi u1 u1 = 1 := by
      calc
        ((F i).metric 0).inner xi u1 u1 =
            g.inner (e i xi) (L u1) (L u1) := hmetric i xi u1 u1
        _ = 1 := by rw [hu1]; exact hv1
    have hu2norm : ((F i).metric 0).inner xi u2 u2 = 1 := by
      calc
        ((F i).metric 0).inner xi u2 u2 =
            g.inner (e i xi) (L u2) (L u2) := hmetric i xi u2 u2
        _ = 1 := by rw [hu2]; exact hv2
    have hu12 : ((F i).metric 0).inner xi u1 u2 = 0 := by
      calc
        ((F i).metric 0).inner xi u1 u2 =
            g.inner (e i xi) (L u1) (L u2) := hmetric i xi u1 u2
        _ = 0 := by rw [hu1, hu2]; exact horth
    have hcurv : ((F i).connection 0).curvatureTensor xi u1 u2 u1 u2 = 0 := by
      calc
        ((F i).connection 0).curvatureTensor xi u1 u2 u1 u2 =
            D.curvatureTensor (e i xi) (L u1) (L u2) (L u1) (L u2) :=
          LeviCivitaData.curvatureTensor_eq_of_local_isometry
            ((F i).connection 0) D isOpen_univ (he i).contMDiff.contMDiffOn
            (fun z _ a b => hmetric i z a b) (mem_univ xi) u1 u2 u1 u2
        _ = 0 := by rw [hu1, hu2]; exact hzero
    have hnorm : ((F i).connection 0).curvatureTensorNorm pi ≠ 0 := by
      rw [LeviCivitaData.curvatureTensorNorm_eq_of_local_isometry
        ((F i).connection 0) D isOpen_univ (he i).contMDiff.contMDiffOn
        (fun z _ a b => hmetric i z a b) (mem_univ pi)]
      exact hnonflat
    exact ricciNullity_eq_one_of_finite_terminal_null_plane
      (ha i) hC (F i) (fun t ht z => hoperator i t ht z)
      ⟨pi, hnorm⟩ xi u1 u2 hu1norm hu2norm hu12 hcurv
  have hnullity : ∀ y : M, ricciNullity D y = 1 := by
    intro y
    obtain ⟨i, hxi, hp0, hy⟩ := hcapture y
    obtain ⟨yi, hyi⟩ := hy
    have hs := hterminal i hxi hp0 yi
    have ht := ricciNullity_eq_of_local_isometry
      ((F i).connection 0) D (he i) (hmetric i) yi
    rw [ht] at hs
    simpa [hyi] using hs
  have hsection : ∀ (y : M) (v : TangentSpace (𝓡 3) y),
      g.inner y v v = 1 →
      (∀ z : TangentSpace (𝓡 3) y, D.ricci y v z = 0) →
      ∃ (U : Set M) (V : (z : M) → TangentSpace (𝓡 3) z),
        IsOpen U ∧ y ∈ U ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
        V y = v ∧
        ∀ z ∈ U, g.inner z (V z) (V z) = 1 ∧
          (∀ w : TangentSpace (𝓡 3) z, D.ricci z (V z) w = 0) ∧
          ∀ w : TangentSpace (𝓡 3) z, D.connection V z w = 0 := by
    intro y v hv hnull
    obtain ⟨i, hxi, hp0, hy⟩ := hcapture y
    obtain ⟨yi, hyi⟩ := hy
    subst y
    have hdim : ∀ z : N i, ricciNullity ((F i).connection 0) z = 1 :=
      hterminal i hxi hp0
    have hsec : ∀ t ∈ Icc (a i) 0,
        ((F i).connection t).NonnegativeSectionalCurvature := by
      intro t ht z u w
      exact ((F i).connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        z (hoperator i t ht z) u w
    exact exists_prescribed_parallel_null_section_of_finite_terminal_local_isometry
      hC (ha i) (F i) hsec hdim D (he i) (hmetric i) yi v hv hnull
  refine ⟨hnullity, ?_⟩
  intro p
  exact hsection p.1.proj p.1.snd p.2.1 p.2.2

end PoincareConjecture.M30
