import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized







open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


theorem PoincareConjecture.NormalizedCornerScalarBound.mono
    {n m k : ℕ} {hdim : n=m+k} {M : Type*}
    [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {δ H η C δ' H' η' C' : ℝ}
    (hb : PoincareConjecture.NormalizedCornerScalarBound n m k hdim M δ H η C)
    (hδ : δ' ≤ δ) (hH : H' ≤ H) (hη : η ≤ η') (hC : C ≤ C') :
    PoincareConjecture.NormalizedCornerScalarBound n m k hdim M δ' H' η' C' := by
  intro g D hc hsec f h hf hh U hunit hpair hcross htight hhess P hP hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m+k) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
  let := openFiberChartedSpace (m := m) hP U hreg c
  let := isManifold_openFiber (m := m) hP U hreg c
  let L := openFiber P U c
  let incl := openFiberIncl P U c
  let gL : PoincareConjecture.RiemannianMetric m L :=
    PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g incl
      (contMDiff_openFiberIncl (m := m) hP U hreg c)
      (injective_mfderiv_openFiberIncl (m := m) hP U hreg c)
  dsimp only
  intro hcompact hconnected hcomplete hdiam hbuffer K hK hKnonneg hKsec
  have hpair' : ∀ x ∈ U, ∀ i,
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1+2*δ := by
    intro x hx i
    exact (hpair x hx i).trans (by linarith)
  have hcross' : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (f i) x) (D.gradient (h j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ δ := by
    intro x hx i j hij
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hcross x hx i j hij
    exact ⟨h₁.trans hδ,h₂.trans hδ,h₃.trans hδ,h₄.trans hδ⟩
  have hhess' : ∀ x ∈ U, ∀ i v,
      D.hessian (f i) x v v ≤ H*g.inner x v v ∧
      D.hessian (h i) x v v ≤ H*g.inner x v v := by
    intro x hx i v
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hv : 0 ≤ g.inner x v v := by
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    exact ⟨(hhess x hx i v).1.trans (mul_le_mul_of_nonneg_right hH hv),
      (hhess x hx i v).2.trans (mul_le_mul_of_nonneg_right hH hv)⟩
  have hbuffer' : ∀ x : L, ∀ y : M, g.edist (incl x) y ≤ ENNReal.ofReal η → y ∈ U :=
    fun x y hxy => hbuffer x y (hxy.trans (ENNReal.ofReal_le_ofReal hη))
  have ht := hb g D hc hsec f h hf hh U hunit hpair' hcross' htight hhess'
    hreg c hcompact hconnected hcomplete hdiam hbuffer' K hK hKnonneg hKsec
  have hi : 0 ≤ ∫ x, K x ∂gL.volumeMeasure := integral_nonneg hKnonneg
  exact ht.trans (mul_le_mul_of_nonneg_right hC (by
    change 0 ≤ 1+∫ x, K x ∂gL.volumeMeasure
    linarith))



theorem PoincareConjecture.NormalizedCornerScalarBound.of_isEmpty
    (n m k : ℕ) (hdim : n=m+k) (M : Type*)
    [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [IsEmpty M] (δ H η C : ℝ) :
    PoincareConjecture.NormalizedCornerScalarBound n m k hdim M δ H η C := by
  classical
  intro g D hc hsec f h hf hh U hunit hpair hcross htight hhess P hP hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m+k) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
  let := openFiberChartedSpace (m := m) hP U hreg c
  let := isManifold_openFiber (m := m) hP U hreg c
  dsimp only
  intro hcompact hconnected
  let : ConnectedSpace (openFiber P U c) := hconnected
  exact isEmptyElim (openFiberIncl P U c (Classical.arbitrary (openFiber P U c)))
