import PoincareConjecture.Proofs.M03.Existence.DeTurckJetCoordinatesNative
import PoincareConjecture.Proofs.M03.Existence.SymmetricTensorHilbertNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorL2Native
import PoincareConjecture.Proofs.M03.Existence.LpFiniteCoordinatesNative









set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.DeTurckCompletedOutputNative

open TensorProbeNative ParsevalTensorNative ChartMeasureNative
  TensorHilbertNative DeTurckJetCoordinatesNative LpFiniteCoordinatesNative

variable {n : ℕ} {M iota : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [Fintype iota]

def multiplyTerms (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  terms.map (fun t => ⟨fun x => c x * t.coefficient x,
    by exact (hc.mul t.smooth).congr (fun x => rfl), t.word⟩)

theorem directionalTerms_multiply
    (F : iota → SmoothField (n := n) (M := M))
    (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (multiplyTerms c hc terms) f x = c x * directionalTerms F terms f x := by
  induction terms with
  | nil => simp only [multiplyTerms, List.map_nil, directionalTerms_nil, mul_zero]
  | cons t terms ih =>
    simp only [multiplyTerms, List.map_cons, directionalTerms_cons] at ih ⊢
    rw [ih]
    ring

theorem multiplyTerms_order
    (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {k : ℕ} (h : ∀ t ∈ terms, t.word.length ≤ k) :
    ∀ t ∈ multiplyTerms c hc terms, t.word.length ≤ k := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact h q hq

def sumTerms {α : Type*} [Fintype α]
    (terms : α → List (DirectionalTerm (n := n) (M := M) (iota := iota))) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) := by
  classical
  exact Finset.univ.toList.flatMap terms

private theorem directionalTerms_flatMap {α : Type*}
    (F : iota → SmoothField (n := n) (M := M)) (s : List α)
    (terms : α → List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (s.flatMap terms) f x =
      (s.map (fun a => directionalTerms F (terms a) f x)).sum := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.flatMap_cons, directionalTerms_append, List.map_cons, List.sum_cons, ih]

theorem directionalTerms_sum
    {α : Type*} [Fintype α] (F : iota → SmoothField (n := n) (M := M))
    (terms : α → List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (sumTerms terms) f x = ∑ a, directionalTerms F (terms a) f x := by
  classical
  rw [sumTerms, directionalTerms_flatMap, Finset.sum_map_toList]

theorem sumTerms_order {α : Type*} [Fintype α]
    (terms : α → List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {k : ℕ} (h : ∀ a t, t ∈ terms a → t.word.length ≤ k) :
    ∀ t ∈ sumTerms terms, t.word.length ≤ k := by
  classical
  intro t ht
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp ht
  exact h a t ha


def laplacianTerms (F : iota → SmoothField (n := n) (M := M))
    (charts : FiniteChartData (n := n) (M := M))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  sumTerms (fun i : iota =>
    multiplyTerms (fun _ : M => (-1 : ℝ)) contMDiff_const
      (differentiateDirectionalTerms F i (differentiateDirectionalTerms F i terms)) ++
    multiplyTerms (fun x => -charts.fieldDivergence (F i) x)
      (charts.fieldDivergence_contMDiff (F i)).neg
      (differentiateDirectionalTerms F i terms))

theorem directionalTerms_laplacian
    (F : iota → SmoothField (n := n) (M := M))
    (charts : FiniteChartData (n := n) (M := M))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (laplacianTerms F charts terms) f x =
      scalarLaplacian F charts (directionalTerms F terms f) x := by
  classical
  rw [laplacianTerms, directionalTerms_sum]
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hfirst : directionalTerms F (differentiateDirectionalTerms F i terms) f =
      scalarDirectional (F i) (directionalTerms F terms f) :=
    funext (directionalTerms_differentiate F i terms hf)
  have hsecond := directionalTerms_differentiate F i
    (differentiateDirectionalTerms F i terms) hf x
  rw [hfirst] at hsecond
  rw [directionalTerms_append, directionalTerms_multiply,
    directionalTerms_multiply, hsecond, hfirst]
  simp only [FiniteChartData.fieldAdjoint]
  ring

theorem laplacianTerms_order
    (F : iota → SmoothField (n := n) (M := M))
    (charts : FiniteChartData (n := n) (M := M))
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {k : ℕ} (h : ∀ t ∈ terms, t.word.length ≤ k) :
    ∀ t ∈ laplacianTerms F charts terms, t.word.length ≤ k + 2 := by
  apply sumTerms_order
  intro i t ht
  have hfirst := differentiateDirectionalTerms_order F i terms h
  have hsecond := differentiateDirectionalTerms_order F i
    (differentiateDirectionalTerms F i terms) hfirst
  rcases List.mem_append.mp ht with ht | ht
  · have hbound := multiplyTerms_order (fun _ : M => (-1 : ℝ)) contMDiff_const
      (differentiateDirectionalTerms F i (differentiateDirectionalTerms F i terms))
      hsecond t ht
    omega
  · have hbound := multiplyTerms_order (fun x => -charts.fieldDivergence (F i) x)
      (charts.fieldDivergence_contMDiff (F i)).neg
      (differentiateDirectionalTerms F i terms) hfirst t ht
    omega

variable {g0 : RiemannianMetric n M} (d : TensorHilbertNative.Data g0)
  [MeasurableSpace M] [BorelSpace M]


def shiftedPowerTerms : ℕ → d.ProbeIndex → d.ProbeIndex →
    List (DirectionalTerm (n := n) (M := M) (iota := Fin d.fieldCount))
  | 0, a, b => if a = b then [⟨fun _ => 1, contMDiff_const, []⟩] else []
  | r + 1, a, b => shiftedPowerTerms r a b ++ sumTerms (fun c : d.ProbeIndex =>
      multiplyTerms (fun x => projectionKernel g0 d.fields x a c)
        (projectionKernel_contMDiff d.fields g0 a c)
        (laplacianTerms d.fields d.charts (shiftedPowerTerms r c b)))

theorem shiftedPowerTerms_order (r : ℕ) (a b : d.ProbeIndex) :
    ∀ t ∈ shiftedPowerTerms d r a b, t.word.length ≤ 2 * r := by
  induction r generalizing a b with
  | zero =>
    intro t ht
    by_cases hab : a = b
    · simp only [shiftedPowerTerms, if_pos hab, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      subst t
      exact Nat.zero_le _
    · simp only [shiftedPowerTerms, if_neg hab, List.not_mem_nil] at ht
  | succ r ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hbound := ih a b t ht
      omega
    · have hbound : t.word.length ≤ 2 * r + 2 := by
        apply sumTerms_order _ (fun c =>
          multiplyTerms_order _ _ _
            (laplacianTerms_order d.fields d.charts _ (ih c b))) t ht
      omega

theorem scalarProbe_shiftedSmoothTensor
    (h : SmoothTensor (n := n) (M := M)) (a : d.ProbeIndex) (x : M) :
    scalarProbe d.fields (d.shiftedSmoothTensor h) a x =
      scalarProbe d.fields h a x + ∑ c : d.ProbeIndex,
        projectionKernel g0 d.fields x a c *
          scalarLaplacian d.fields d.charts (scalarProbe d.fields h c) x := by
  classical
  change scalarProbe d.fields h a x +
    probes d.fields (smoothTensorLaplacian d.fields d.charts g0 h) x a = _
  rw [probes_smoothTensorLaplacian, nativeProjection_eq_kernel]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _


theorem scalarProbe_shiftedSmoothPower (r : ℕ)
    (h : SmoothTensor (n := n) (M := M)) (a : d.ProbeIndex) (x : M) :
    scalarProbe d.fields (d.shiftedSmoothPower r h) a x =
      ∑ b : d.ProbeIndex,
        directionalTerms d.fields (shiftedPowerTerms d r a b) (scalarProbe d.fields h b) x := by
  classical
  induction r generalizing a x with
  | zero =>
    have hz (b : d.ProbeIndex) :
        directionalTerms d.fields (shiftedPowerTerms d 0 a b) (scalarProbe d.fields h b) x =
          if a = b then scalarProbe d.fields h b x else 0 := by
      by_cases hab : a = b <;>
        simp [shiftedPowerTerms, hab, directionalTerms, directionalWord]
    simp only [TensorHilbertNative.Data.shiftedSmoothPower]
    simp_rw [hz]
    simp
  | succ r ih =>
    rw [TensorHilbertNative.Data.shiftedSmoothPower, scalarProbe_shiftedSmoothTensor, ih]
    simp only [shiftedPowerTerms, directionalTerms_append, directionalTerms_sum,
      directionalTerms_multiply,
      directionalTerms_laplacian d.fields d.charts _ (scalarProbe_contMDiff d.fields h _)]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.mul_sum]
    congr 1
    have heq : scalarProbe d.fields (d.shiftedSmoothPower r h) c =
        fun y => ∑ b : d.ProbeIndex,
          directionalTerms d.fields (shiftedPowerTerms d r c b) (scalarProbe d.fields h b) y :=
      funext (ih c)
    rw [heq]
    exact scalarLaplacian_finsetSum d.fields d.charts Finset.univ isOpen_univ _
      (fun b _ => (directionalTerms_contMDiff d.fields _
        (scalarProbe_contMDiff d.fields h b)).contMDiffOn) (mem_univ x)

abbrev ProbeTuples (k : ℕ) :=
  d.ProbeIndex → WordIndex (Fin d.fieldCount) k → Lp ℝ 2 d.charts.measure


def powerProbeL2 (r : ℕ) (a : d.ProbeIndex) :
    ProbeTuples d (2 * r) →L[ℝ] Lp ℝ 2 d.charts.measure :=
  ∑ b : d.ProbeIndex,
    (termsL2 d.charts.measure (shiftedPowerTerms d r a b)
      (shiftedPowerTerms_order d r a b)).comp (ContinuousLinearMap.proj b)

theorem powerProbeL2_ae_eq (r : ℕ) (a : d.ProbeIndex)
    (Q : ProbeTuples d (2 * r)) (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ b w (hw : w.length ≤ 2 * r),
      Q b (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (scalarProbe d.fields h b)) :
    powerProbeL2 d r a Q =ᵐ[d.charts.measure]
      scalarProbe d.fields (d.shiftedSmoothPower r h) a := by
  let q (b : d.ProbeIndex) : Lp ℝ 2 d.charts.measure :=
    termsL2 d.charts.measure (shiftedPowerTerms d r a b)
      (shiftedPowerTerms_order d r a b) (Q b)
  have hq (b : d.ProbeIndex) : q b =ᵐ[d.charts.measure]
      directionalTerms d.fields (shiftedPowerTerms d r a b) (scalarProbe d.fields h b) :=
    termsL2_ae_eq d.fields d.charts.measure (shiftedPowerTerms d r a b)
      (shiftedPowerTerms_order d r a b) (Q b) (scalarProbe d.fields h b) (hQ b)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq]
    with x hsum hterms
  simp only [powerProbeL2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ b : d.ProbeIndex, q b) x = _
  rw [hsum]
  simp only [hterms]
  exact (scalarProbe_shiftedSmoothPower d r h a x).symm


def powerTensorL2 (r : ℕ) :
    ProbeTuples d (2 * r) →L[ℝ] Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure :=
  ∑ a : d.ProbeIndex, (insertionLp d.charts.measure a).comp (powerProbeL2 d r a)

theorem powerTensorL2_eq (r : ℕ) (Q : ProbeTuples d (2 * r))
    (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ b w (hw : w.length ≤ 2 * r),
      Q b (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (scalarProbe d.fields h b)) :
    powerTensorL2 d r Q = tensorToLp d.fields d.charts.measure (d.shiftedSmoothPower r h) := by
  let q (a : d.ProbeIndex) := powerProbeL2 d r a Q
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun a : d.ProbeIndex => insertionLp d.charts.measure a (q a)),
    ae_all_iff.mpr (fun a : d.ProbeIndex => insertionLp_coe d.charts.measure a (q a)),
    ae_all_iff.mpr (fun a : d.ProbeIndex => powerProbeL2_ae_eq d r a Q h hQ),
    tensorToLp_coe d.fields d.charts.measure (d.shiftedSmoothPower r h)]
    with x hsum hinsert hprobe htensor
  simp only [powerTensorL2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ a : d.ProbeIndex, insertionLp d.charts.measure a (q a)) x = _
  rw [hsum, htensor]
  calc
    _ = ∑ a : d.ProbeIndex, scalarProbe d.fields (d.shiftedSmoothPower r h) a x •
        EuclideanSpace.basisFun d.ProbeIndex ℝ a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hinsert a]
      change powerProbeL2 d r a Q x • _ = _
      rw [hprobe a]
    _ = _ := sum_coordinates (probes d.fields (d.shiftedSmoothPower r h) x)

def projectedValue :
    Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure →L[ℝ] d.Value :=
  (tensorL2 d.fields d.charts.measure).orthogonalProjectionOnto

@[simp] theorem projectedValue_eq_self (v : d.Value) :
    projectedValue d (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) = v :=
  (tensorL2 d.fields d.charts.measure).orthogonalProjectionOnto_mem_subspace_eq_self v


theorem projectedValue_eq_of_projection
    (f : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) (v : d.Value)
    (hf : projectionL2 g0 d.fields d.parseval d.charts.measure f =
      (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure)) :
    projectedValue d f = v := by
  apply Subtype.ext
  change (tensorL2 d.fields d.charts.measure).starProjection f = (v : Lp _ 2 _)
  apply (tensorL2 d.fields d.charts.measure).eq_starProjection_of_mem_of_inner_eq_zero
    v.property
  intro w hw
  rw [inner_sub_left, ← hf, projectionL2_selfadjoint,
    projectionL2_eq_self_of_mem_tensorL2 g0 d.fields d.parseval d.charts.measure hw,
    sub_self]


def evenOutput (r : ℕ) :
    ProbeTuples d (2 * r) →L[ℝ] SpectralHeatNative.State d.SymmetricIndex :=
  d.symmetricBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((d.valueSymmetrize.codRestrict d.symmetricValue d.valueSymmetrize_mem).comp
      ((projectedValue d).comp (powerTensorL2 d r)))

theorem evenOutput_eq (r : ℕ) (Q : ProbeTuples d (2 * r))
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (hQ : ∀ b w (hw : w.length ≤ 2 * r),
      Q b (wordIndex w hw) =ᵐ[d.charts.measure]
        directionalWord d.fields w (scalarProbe d.fields h b)) :
    evenOutput d r Q = d.smoothTensorCoordinates (2 * r) h hsymm := by
  have hvalue : projectedValue d (powerTensorL2 d r Q) =
      intoTensorL2 d.fields d.charts.measure (d.shiftedSmoothPower r h) := by
    rw [powerTensorL2_eq d r Q h hQ]
    exact projectedValue_eq_self d
      (intoTensorL2 d.fields d.charts.measure (d.shiftedSmoothPower r h))
  have hsym : (d.valueSymmetrize.codRestrict d.symmetricValue d.valueSymmetrize_mem)
      (projectedValue d (powerTensorL2 d r Q)) =
      d.intoSymmetricValue (d.shiftedSmoothPower r h) (d.shiftedSmoothPower_symm r h hsymm) := by
    apply Subtype.ext
    change d.valueSymmetrize (projectedValue d (powerTensorL2 d r Q)) = _
    rw [hvalue]
    exact d.valueSymmetrize_eq_self_of_mem
      (d.intoSymmetricValue (d.shiftedSmoothPower r h)
        (d.shiftedSmoothPower_symm r h hsymm)).property
  change d.symmetricBasis.repr
    ((d.valueSymmetrize.codRestrict d.symmetricValue d.valueSymmetrize_mem)
      (projectedValue d (powerTensorL2 d r Q))) = _
  rw [hsym]
  exact (d.scaleEncode_even_smoothTensor r h hsymm).symm

theorem evenOutput_norm_le (r : ℕ) (Q : ProbeTuples d (2 * r)) :
    ‖evenOutput d r Q‖ ≤ ‖evenOutput d r‖ * ‖Q‖ :=
  (evenOutput d r).le_opNorm Q

def smoothProbeTuples (k : ℕ) (h : SmoothTensor (n := n) (M := M)) : ProbeTuples d k :=
  fun b w => ContinuousMap.toLp 2 d.charts.measure ℝ
    ⟨directionalWord d.fields (List.ofFn w.2) (scalarProbe d.fields h b),
      (directionalWord_contMDiff d.fields (List.ofFn w.2)
        (scalarProbe_contMDiff d.fields h b)).continuous⟩

theorem smoothProbeTuples_ae_eq (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (b : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    smoothProbeTuples d k h b (wordIndex w hw) =ᵐ[d.charts.measure]
      directionalWord d.fields w (scalarProbe d.fields h b) := by
  simpa only [smoothProbeTuples, wordIndex_word, ContinuousMap.coe_mk] using
    ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (μ := d.charts.measure) (𝕜 := ℝ)
      (⟨directionalWord d.fields w (scalarProbe d.fields h b),
        (directionalWord_contMDiff d.fields w (scalarProbe_contMDiff d.fields h b)).continuous⟩ :
          C(M, ℝ))

theorem evenOutput_smoothProbeTuples (r : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    evenOutput d r (smoothProbeTuples d (2 * r) h) =
      d.smoothTensorCoordinates (2 * r) h hsymm :=
  evenOutput_eq d r _ h hsymm (smoothProbeTuples_ae_eq d (2 * r) h)

end PoincareConjecture.DeTurckCompletedOutputNative

end
