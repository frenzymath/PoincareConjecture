import PoincareConjecture.Proofs.M47.TerminalGermsExhaustionFlows
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.M47



theorem terminalGerms_descended_operator
    {n : ℕ} {ι : Type*} {P : ι → Type*} {M : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace M]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ M]
    (tau : ι → ℝ) (F : ∀ i, RicciFlow n (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (U : Opens M) (s : Finset ι)
    (hcover : ∀ y ∈ U, ∃ i ∈ s, ∃ x, q i x = y)
    {delta : ℝ} (hdelta : ∀ i ∈ s, delta < tau i)
    (G : RicciFlow n U (Icc (-delta) 0))
    (hread : ∀ t ∈ Icc (-delta) 0, ∀ i, t ∈ Icc (-tau i) 0 →
      ∀ (x : P i) (hx : q i x ∈ U) (a b : TangentSpace (𝓡 n) x),
        ((F i).metric t).inner x a b = (G.metric t).inner ⟨q i x, hx⟩
          (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (hoperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ x,
      ((F i).connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Icc (-delta) 0, ∀ y, (G.connection t).NonnegativeCurvatureOperator y := by
  intro t ht y
  obtain ⟨i, hi, x, hxy⟩ := hcover y.val y.property
  have hti : t ∈ Icc (-tau i) 0 :=
    ⟨(neg_le_neg (hdelta i hi).le).trans ht.1, ht.2⟩
  have hx : q i x ∈ U := hxy.symm ▸ y.property
  let W := terminalGermsOpenChartSource (q i) (hq i) U
  let H := (F i).restrictToOpen W
  let z : W := ⟨x, hx⟩
  have hsource : (H.connection t).NonnegativeCurvatureOperator z := by
    apply ((H.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      ((F i).connection t) (f := (Subtype.val : W → P i)) isOpen_univ
      contMDiff_subtype_val.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ z)).mpr
    exact hoperator i t hti x
  have hmetric : ∀ w ∈ (univ : Set W), ∀ a b : TangentSpace (𝓡 n) w,
      (H.metric t).inner w a b = (G.metric t).inner
        (terminalGermsOpenChartMap (q i) (hq i) U w)
        (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap (q i) (hq i) U) w a)
        (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap (q i) (hq i) U) w b) := by
    intro w _ a b
    change ((F i).metric t).inner w.val
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : W → P i) w a)
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : W → P i) w b) = _
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply,
      Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply,
      terminalGerms_openChartMap_mfderiv]
    exact hread t ht i hti w.val w.property a b
  have htarget := ((H.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (G.connection t) (f := terminalGermsOpenChartMap (q i) (hq i) U)
    (U := univ) isOpen_univ
    (terminalGerms_openChartMap_localDiffeomorph (q i) (hq i) U).contMDiff.contMDiffOn
    hmetric (x := z) (mem_univ z)).mp hsource
  have hz : terminalGermsOpenChartMap (q i) (hq i) U z = y := Subtype.ext hxy
  exact hz ▸ htarget



theorem terminalGerms_ambient_operator_of_exhaustion
    {n : ℕ} {ι : Type*} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (U : ι → Opens M) (delta : ι → ℝ) (hdelta : ∀ i, 0 < delta i)
    (G : ∀ i, RicciFlow n (U i) (Icc (-delta i) 0))
    (hmetric : ∀ i (y : U i) (v w : TangentSpace (𝓡 n) y),
      ((G i).metric 0).inner y v w = g.inner y.val v w)
    (hoperator : ∀ i t, t ∈ Icc (-delta i) 0 → ∀ y,
      ((G i).connection t).NonnegativeCurvatureOperator y)
    (hcover : ∀ y, ∃ i, y ∈ U i) :
    ∀ y, D.NonnegativeCurvatureOperator y := by
  intro y
  obtain ⟨i, hi⟩ := hcover y
  let z : U i := ⟨y, hi⟩
  have hzero : (0 : ℝ) ∈ Icc (-delta i) 0 := ⟨by linarith [hdelta i], le_rfl⟩
  have hm : ∀ z ∈ (univ : Set (U i)), ∀ v w : TangentSpace (𝓡 n) z,
      ((G i).metric 0).inner z v w = g.inner z.val
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U i → M) z v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U i → M) z w) := by
    intro z _ v w
    simpa only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
      using hmetric i z v w
  exact (((G i).connection 0).nonnegativeCurvatureOperator_iff_of_local_isometry
    D (f := (Subtype.val : U i → M)) (U := univ) isOpen_univ
    contMDiff_subtype_val.contMDiffOn hm (x := z) (mem_univ z)).mp
      (hoperator i 0 hzero z)

end PoincareConjecture.M47
