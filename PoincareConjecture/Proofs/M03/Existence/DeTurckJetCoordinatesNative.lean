import PoincareConjecture.Proofs.M03.Existence.DeTurckCompatibleJetNative
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions









set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.DeTurckJetCoordinatesNative

open TensorProbeNative DeTurckCompatibleJetNative DeTurckNative
  DeTurckInverseCompositionNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota jota : Type*} [Fintype iota]

def scaleTerms (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  terms.map (fun t => {
    coefficient := fun x => c x * t.coefficient x
    smooth := by
      exact hc.mul (g := t.coefficient) t.smooth
    word := t.word })

theorem directionalTerms_scale (F : iota → SmoothField (n := n) (M := M))
    (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (scaleTerms c hc terms) f x = c x * directionalTerms F terms f x := by
  induction terms with
  | nil => simp [scaleTerms]
  | cons t terms ih =>
    change (c x * t.coefficient x) * directionalWord F t.word f x +
      directionalTerms F (scaleTerms c hc terms) f x =
        c x * (t.coefficient x * directionalWord F t.word f x + directionalTerms F terms f x)
    rw [ih]
    ring

theorem directionalTerms_flatMap {α : Type*}
    (F : iota → SmoothField (n := n) (M := M)) (l : List α)
    (terms : α → List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (f : M → ℝ) (x : M) :
    directionalTerms F (l.flatMap terms) f x =
      (l.map (fun a => directionalTerms F (terms a) f x)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, directionalTerms_append, ih]
    rfl

variable (F : iota → SmoothField (n := n) (M := M))
  (coefficient : jota → iota → M → ℝ)
  (hcoefficient : ∀ a i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (coefficient a i))

def expandedDerivative (a : jota)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  Finset.univ.toList.flatMap (fun i => scaleTerms (coefficient a i) (hcoefficient a i)
    (differentiateDirectionalTerms F i terms))

theorem expandedDerivative_order (a : jota)
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {k : ℕ} (h : ∀ t ∈ terms, t.word.length ≤ k) :
    ∀ t ∈ expandedDerivative F coefficient hcoefficient a terms, t.word.length ≤ k + 1 := by
  intro t ht
  obtain ⟨i, _, ht⟩ := List.mem_flatMap.mp ht
  dsimp only [scaleTerms] at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact differentiateDirectionalTerms_order F i terms h s hs

theorem expandedDerivative_eq
    (V : jota → SmoothField (n := n) (M := M))
    (hV : ∀ a x, V a x = ∑ i, coefficient a i x • F i x)
    (a : jota) (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (expandedDerivative F coefficient hcoefficient a terms) f x =
      scalarDirectional (V a) (directionalTerms F terms f) x := by
  simp only [expandedDerivative, directionalTerms_flatMap, directionalTerms_scale,
    directionalTerms_differentiate F _ _ hf, Finset.sum_map_toList]
  change (∑ i, coefficient a i x * scalarDirectional (F i) (directionalTerms F terms f) x) =
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalTerms F terms f) x (V a x)
  rw [hV a x, map_sum]
  simp only [map_smul, scalarDirectional]
  rfl

def wordTerms : List jota → List (DirectionalTerm (n := n) (M := M) (iota := iota))
  | [] => [⟨fun _ => 1, contMDiff_const, []⟩]
  | a :: w => expandedDerivative F coefficient hcoefficient a
      (wordTerms w)

theorem wordTerms_order (w : List jota) :
    ∀ t ∈ wordTerms F coefficient hcoefficient w, t.word.length ≤ w.length := by
  induction w with
  | nil =>
    intro t ht
    have ht' : t = ⟨fun _ => 1, contMDiff_const, []⟩ := List.mem_singleton.mp ht
    subst t
    exact le_rfl
  | cons a w ih => exact expandedDerivative_order F coefficient hcoefficient a _ ih

theorem wordTerms_eq
    (V : jota → SmoothField (n := n) (M := M))
    (hV : ∀ a x, V a x = ∑ i, coefficient a i x • F i x)
    (w : List jota) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (wordTerms F coefficient hcoefficient w) f x =
      directionalWord V w f x := by
  induction w generalizing x with
  | nil => simp [wordTerms]
  | cons a w ih =>
    rw [wordTerms, expandedDerivative_eq F coefficient hcoefficient V hV _ _ hf]
    exact congrArg (fun g : M → ℝ => scalarDirectional (V a) g x) (funext ih)

section Compatible

variable [T2Space M] [CompactSpace M] {p : M} {K : Set M} (C : Cutoffs (n := n) p K)

def combinedFields : Fin n ⊕ iota → SmoothField (n := n) (M := M) :=
  Sum.elim C.field F

def combinedCoefficient (g0 : RiemannianMetric n M) : (Fin n ⊕ iota) → iota → M → ℝ := by
  classical
  exact Sum.elim (C.fieldCoefficient g0 F) (fun a i _ => if a = i then 1 else 0)

theorem combinedCoefficient_contMDiff (g0 : RiemannianMetric n M)
    (a : Fin n ⊕ iota) (i : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (combinedCoefficient F C g0 a i) := by
  cases a with
  | inl a => exact C.fieldCoefficient_contMDiff g0 F a i
  | inr a => exact contMDiff_const

theorem combinedFields_eq_sum (g0 : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v) (a : Fin n ⊕ iota) (x : M) :
    combinedFields F C a x = ∑ i, combinedCoefficient F C g0 a i x • F i x := by
  classical
  cases a with
  | inl a => exact C.field_eq_sum g0 F hF a x
  | inr a => simp [combinedFields, combinedCoefficient]

def combinedWordTerms (g0 : RiemannianMetric n M) (w : List (Fin n ⊕ iota)) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  wordTerms F (combinedCoefficient F C g0) (combinedCoefficient_contMDiff F C g0) w

theorem combinedWordTerms_order (g0 : RiemannianMetric n M)
    (w : List (Fin n ⊕ iota)) :
    ∀ t ∈ combinedWordTerms F C g0 w, t.word.length ≤ w.length :=
  wordTerms_order F (combinedCoefficient F C g0) (combinedCoefficient_contMDiff F C g0) w

theorem combinedWordTerms_eq (g0 : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v)
    (w : List (Fin n ⊕ iota)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (combinedWordTerms F C g0 w) f x =
      directionalWord (combinedFields F C) w f x :=
  wordTerms_eq F (combinedCoefficient F C g0) (combinedCoefficient_contMDiff F C g0)
    (combinedFields F C) (combinedFields_eq_sum F C g0 hF) w hf x

theorem matrix_word_eq_native (g0 g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v)
    (w : List (Fin n ⊕ iota)) (i j : Fin n) (x : M) :
    directionalWord (combinedFields F C) w (fun y => C.matrix g y i j) x =
      directionalTerms F (combinedWordTerms F C g0 w) (fun y => C.matrix g y i j) x :=
  (combinedWordTerms_eq F C g0 hF w (C.matrix_entry_contMDiff g i j) x).symm

end Compatible

section ChartOutput

variable [T2Space M] [CompactSpace M] {p : M} {K : Set M} (C : Cutoffs (n := n) p K)


def dualCoefficient (g0 : RiemannianMetric n M) (V : SmoothField (n := n) (M := M))
    (i : Fin n) (x : M) : ℝ :=
  ∑ k, (C.matrix g0 x)⁻¹ i k * g0.inner x (C.field k x) (V x)

theorem dualCoefficient_contMDiff (g0 : RiemannianMetric n M)
    (V : SmoothField (n := n) (M := M)) (i : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (dualCoefficient C g0 V i) := by
  apply contMDiff_finsetSum
  intro k _
  exact (inverse_entry_contMDiff (C.matrix g0) (C.matrix_contMDiff g0)
    (fun x => ((C.matrix g0 x).isUnit_iff_isUnit_det.mp
      (C.matrix_posDef g0 x).isUnit).ne_zero) i k).mul
    (contMDiff_pairing (metricTensor g0) (C.field k) V)

theorem dualCoefficient_eq_repr (g0 : RiemannianMetric n M)
    (V : SmoothField (n := n) (M := M)) {x : M} (hx : x ∈ K) (i : Fin n) :
    dualCoefficient C g0 V i x =
      (chartFrameBasis p x (C.eta_support (C.mem_eta_support hx))).repr (V x) i := by
  let b := chartFrameBasis p x (C.eta_support (C.mem_eta_support hx))
  have hfield (k : Fin n) : C.field k x = b k := by
    rw [(C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) k).eq_of_nhds]
    exact chartFrame_eq_basis p x _ k
  have hmatrix (k j : Fin n) : C.matrix g0 x k j = g0.inner x (b k) (b j) := by
    rw [(C.matrix_eventuallyEq g0 (C.eta_one x hx)).eq_of_nhds]
    change g0.inner x (chartFrame p k x) (chartFrame p j x) = _
    rw [chartFrame_eq_basis p x _ k, chartFrame_eq_basis p x _ j]
  have hpair : (fun k => g0.inner x (C.field k x) (V x)) =
      (C.matrix g0 x).mulVec (fun j => b.repr (V x) j) := by
    funext k
    change g0.inner x (C.field k x) (V x) = ∑ j, C.matrix g0 x k j * b.repr (V x) j
    calc
      _ = g0.inner x (b k) (∑ j, b.repr (V x) j • b j) := by
        rw [b.sum_repr, hfield]
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul, hmatrix]
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
  have hinv := (C.matrix g0 x).nonsing_inv_mul
    ((C.matrix g0 x).isUnit_iff_isUnit_det.mp (C.matrix_posDef g0 x).isUnit)
  change ((C.matrix g0 x)⁻¹.mulVec (fun k => g0.inner x (C.field k x) (V x))) i = _
  rw [hpair, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem sum_dualCoefficient_field (g0 : RiemannianMetric n M)
    (V : SmoothField (n := n) (M := M)) {x : M} (hx : x ∈ K) :
    (∑ i, dualCoefficient C g0 V i x • C.field i x) = V x := by
  let b := chartFrameBasis p x (C.eta_support (C.mem_eta_support hx))
  calc
    _ = ∑ i, b.repr (V x) i • b i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dualCoefficient_eq_repr C g0 V hx i,
        (C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) i).eq_of_nhds,
        chartFrame_eq_basis p x _ i]
    _ = _ := b.sum_repr (V x)

def outputCoefficient (g0 : RiemannianMetric n M) (chi : M → ℝ)
    (V W : SmoothField (n := n) (M := M)) (i j : Fin n) (x : M) : ℝ :=
  chi x * dualCoefficient C g0 V i x * dualCoefficient C g0 W j x

theorem outputCoefficient_contMDiff (g0 : RiemannianMetric n M) {chi : M → ℝ}
    (hchi : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ chi)
    (V W : SmoothField (n := n) (M := M)) (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (outputCoefficient C g0 chi V W i j) :=
  (hchi.mul (dualCoefficient_contMDiff C g0 V i)).mul
    (dualCoefficient_contMDiff C g0 W j)


theorem weighted_bilinear_eq (g0 : RiemannianMetric n M) (chi : M → ℝ)
    (hchi : Function.support chi ⊆ K) (V W : SmoothField (n := n) (M := M))
    (B : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (x : M) :
    chi x * B x (V x) (W x) =
      ∑ i, ∑ j, outputCoefficient C g0 chi V W i j x *
        B x (C.field i x) (C.field j x) := by
  by_cases hx : x ∈ K
  · conv_lhs =>
      arg 2
      rw [← sum_dualCoefficient_field C g0 V hx, ← sum_dualCoefficient_field C g0 W hx]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, outputCoefficient]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have hz : chi x = 0 := by
      by_contra h
      exact hx (hchi h)
    simp only [hz, outputCoefficient, zero_mul, Finset.sum_const_zero]

theorem weighted_source_eq (g0 : RiemannianMetric n M) (chi : M → ℝ)
    (hchi : Function.support chi ⊆ K) (V W : SmoothField (n := n) (M := M))
    (B : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (S : M → Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ x ∈ K, ∀ i j, S x i j = B x (C.field i x) (C.field j x)) (x : M) :
    chi x * B x (V x) (W x) =
      ∑ i, ∑ j, outputCoefficient C g0 chi V W i j x * S x i j := by
  rw [weighted_bilinear_eq C g0 chi hchi V W B x]
  by_cases hx : x ∈ K
  · simp only [hS x hx]
  · have hz : chi x = 0 := by
      by_contra h
      exact hx (hchi h)
    simp only [outputCoefficient, hz, zero_mul, Finset.sum_const_zero]


theorem weighted_ricciDeTurck_eq (g0 g : RiemannianMetric n M)
    (D : LeviCivitaData g) (B : LeviCivitaData g0) (chi : M → ℝ)
    (hchi : Function.support chi ⊆ K) (V W : SmoothField (n := n) (M := M)) (x : M) :
    chi x * smoothRicciDeTurckTensor D B x (V x) (W x) =
      ∑ i, ∑ j, outputCoefficient C g0 chi V W i j x *
        ricciDeTurckSource (C.jet g0 x) (C.jet g x) i j := by
  apply weighted_source_eq C g0 chi hchi V W (smoothRicciDeTurckTensor D B)
  intro y hy i j
  rw [C.jet_eq_on g0 hy, C.jet_eq_on g hy,
    (C.field_eventuallyEq (C.zeta_one y (C.mem_eta_support hy)) i).eq_of_nhds,
    (C.field_eventuallyEq (C.zeta_one y (C.mem_eta_support hy)) j).eq_of_nhds,
    smoothRicciDeTurckTensor_apply]
  exact ricciDeTurckSource_frameMetricJet_eq_intrinsic D B p
    (C.eta_support (C.mem_eta_support hy)) i j


theorem ricciDeTurck_eq_sum_chartSources {A : Type*} [Fintype A]
    (centers : A → M) (sets : A → Set M) (cutoffs : ∀ a, Cutoffs (n := n) (centers a) (sets a))
    (chi : A → M → ℝ) (hchi : ∀ a, Function.support (chi a) ⊆ sets a)
    (hsum : ∀ x, ∑ a, chi a x = 1) (g0 g : RiemannianMetric n M)
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (V W : SmoothField (n := n) (M := M)) (x : M) :
    smoothRicciDeTurckTensor D B x (V x) (W x) =
      ∑ a, ∑ i, ∑ j, outputCoefficient (cutoffs a) g0 (chi a) V W i j x *
        ricciDeTurckSource ((cutoffs a).jet g0 x) ((cutoffs a).jet g x) i j := by
  calc
    _ = ∑ a, chi a x * smoothRicciDeTurckTensor D B x (V x) (W x) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ = _ := Finset.sum_congr rfl (fun a _ =>
      weighted_ricciDeTurck_eq (cutoffs a) g0 g D B (chi a) (hchi a) V W x)

end ChartOutput

section FiniteCover

variable [T2Space M] [CompactSpace M]

structure CompatibleChartCover where
  centers : Finset M
  partition : SmoothPartitionOfUnity centers (𝓡 n) M Set.univ
  cutoffs : ∀ a : centers, Cutoffs (n := n) a.val (tsupport (partition a))


theorem exists_compatibleChartCover : Nonempty (CompatibleChartCover (n := n) (M := M)) := by
  classical
  let U : M → Set M := fun p => (chartAt (EuclideanSpace ℝ (Fin n)) p).source
  have hcover : Set.univ ⊆ ⋃ p : M, U p := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun p => (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source) hcover
  have hscover : Set.univ ⊆ ⋃ a : s, U a.val := by
    intro x hx
    have hxs := hs hx
    simp only [Set.mem_iUnion] at hxs
    obtain ⟨p, hp, hxp⟩ := hxs
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨rho, hrho⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n)
    isClosed_univ (fun a : s => U a.val)
    (fun a => (chartAt (EuclideanSpace ℝ (Fin n)) a.val).open_source) hscover
  exact ⟨{
    centers := s
    partition := rho
    cutoffs := fun a => Classical.choice
      (exists_cutoffs a.val (isClosed_tsupport (rho a)).isCompact (hrho a)) }⟩

namespace CompatibleChartCover

variable (A : CompatibleChartCover (n := n) (M := M))

theorem weight_sum (x : M) : (∑ a : A.centers, A.partition a x) = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using A.partition.sum_eq_one (Set.mem_univ x)

theorem source_eq (g0 g : RiemannianMetric n M) (D : LeviCivitaData g)
    (B : LeviCivitaData g0) (V W : SmoothField (n := n) (M := M)) (x : M) :
    smoothRicciDeTurckTensor D B x (V x) (W x) =
      ∑ a : A.centers, ∑ i, ∑ j,
        outputCoefficient (A.cutoffs a) g0 (A.partition a) V W i j x *
          ricciDeTurckSource ((A.cutoffs a).jet g0 x) ((A.cutoffs a).jet g x) i j :=
  ricciDeTurck_eq_sum_chartSources (fun a : A.centers => a.val)
    (fun a => tsupport (A.partition a)) A.cutoffs (fun a => A.partition a)
    (fun a => subset_tsupport (A.partition a)) A.weight_sum g0 g D B V W x

end CompatibleChartCover

end FiniteCover

section CompletedTuples

open MeasureTheory Filter

variable [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsFiniteMeasure μ]

abbrev WordIndex (iota : Type*) (k : ℕ) := Σ l : Fin (k + 1), Fin l.val → iota

def wordIndex (w : List iota) {k : ℕ} (hw : w.length ≤ k) : WordIndex iota k :=
  ⟨⟨w.length, by omega⟩, w.get⟩

theorem wordIndex_word (w : List iota) {k : ℕ} (hw : w.length ≤ k) :
    List.ofFn (wordIndex w hw).2 = w := by
  exact List.ofFn_get w

def coefficientL2 (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ (⊤ : ENNReal) 2 2
    (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ ⟨c, hc.continuous⟩)

theorem coefficientL2_coe (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (q : Lp ℝ 2 μ) : coefficientL2 μ c hc q =ᵐ[μ] fun x => c x * q x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := (2 : ENNReal))
    (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ ⟨c, hc.continuous⟩) q,
    ContinuousMap.coeFn_toLp (p := (⊤ : ENNReal)) (μ := μ) (𝕜 := ℝ)
      (⟨c, hc.continuous⟩ : C(M, ℝ))] with x hx hc'
  change coefficientL2 μ c hc q x =
    (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ ⟨c, hc.continuous⟩) x * q x at hx
  rw [hc'] at hx
  exact hx

def termsL2 {k : ℕ} :
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) →
    (∀ t ∈ terms, t.word.length ≤ k) →
    (WordIndex iota k → Lp ℝ 2 μ) →L[ℝ] Lp ℝ 2 μ
  | [], _ => 0
  | t :: terms, h =>
      (coefficientL2 μ t.coefficient t.smooth).comp
        (ContinuousLinearMap.proj (wordIndex t.word (h t List.mem_cons_self))) +
      termsL2 terms (fun s hs => h s (List.mem_cons_of_mem t hs))


theorem termsL2_ae_eq {k : ℕ}
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (h : ∀ t ∈ terms, t.word.length ≤ k)
    (Q : WordIndex iota k → Lp ℝ 2 μ) (f : M → ℝ)
    (hQ : ∀ w (hw : w.length ≤ k),
      Q (wordIndex w hw) =ᵐ[μ] directionalWord F w f) :
    termsL2 μ terms h Q =ᵐ[μ] directionalTerms F terms f := by
  induction terms with
  | nil =>
    change (0 : Lp ℝ 2 μ) =ᵐ[μ] (0 : M → ℝ)
    exact Lp.coeFn_zero ℝ 2 μ
  | cons t terms ih =>
    let q := Q (wordIndex t.word (h t List.mem_cons_self))
    let rest := termsL2 μ terms (fun s hs => h s (List.mem_cons_of_mem t hs)) Q
    have hrest : rest =ᵐ[μ] directionalTerms F terms f := ih _
    filter_upwards [coefficientL2_coe μ t.coefficient t.smooth q,
      hQ t.word (h t List.mem_cons_self), hrest,
      Lp.coeFn_add (coefficientL2 μ t.coefficient t.smooth q) rest]
      with x hx hqx hrx hadd
    change (coefficientL2 μ t.coefficient t.smooth q + rest) x = _
    rw [hadd, Pi.add_apply, hx, hqx, hrx]
    rfl

variable {p : M} {K : Set M} (C : Cutoffs (n := n) p K)

def combinedWordL2 (g0 : RiemannianMetric n M) (w : List (Fin n ⊕ iota)) :
    (WordIndex iota w.length → Lp ℝ 2 μ) →L[ℝ] Lp ℝ 2 μ :=
  termsL2 μ (combinedWordTerms F C g0 w) (combinedWordTerms_order F C g0 w)

theorem combinedWordL2_ae_eq (g0 : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v)
    (w : List (Fin n ⊕ iota)) (Q : WordIndex iota w.length → Lp ℝ 2 μ)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hQ : ∀ v (hv : v.length ≤ w.length),
      Q (wordIndex v hv) =ᵐ[μ] directionalWord F v f) :
    combinedWordL2 F μ C g0 w Q =ᵐ[μ] directionalWord (combinedFields F C) w f := by
  have h := termsL2_ae_eq F μ (combinedWordTerms F C g0 w)
    (combinedWordTerms_order F C g0 w) Q f hQ
  exact h.mono (fun x hx => hx.trans (combinedWordTerms_eq F C g0 hF w hf x))

def termsContinuous {k : ℕ} :
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota))) →
    (∀ t ∈ terms, t.word.length ≤ k) →
    (WordIndex iota k → C(M, ℝ)) →L[ℝ] C(M, ℝ)
  | [], _ => 0
  | t :: terms, h =>
      (ContinuousLinearMap.mul ℝ C(M, ℝ) ⟨t.coefficient, t.smooth.continuous⟩).comp
        (ContinuousLinearMap.proj (wordIndex t.word (h t List.mem_cons_self))) +
      termsContinuous terms (fun s hs => h s (List.mem_cons_of_mem t hs))

theorem termsContinuous_eq {k : ℕ}
    (terms : List (DirectionalTerm (n := n) (M := M) (iota := iota)))
    (h : ∀ t ∈ terms, t.word.length ≤ k)
    (Q : WordIndex iota k → C(M, ℝ)) (f : M → ℝ)
    (hQ : ∀ w (hw : w.length ≤ k) x,
      Q (wordIndex w hw) x = directionalWord F w f x) (x : M) :
    termsContinuous terms h Q x = directionalTerms F terms f x := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    change t.coefficient x * Q (wordIndex t.word (h t List.mem_cons_self)) x +
      termsContinuous terms (fun s hs => h s (List.mem_cons_of_mem t hs)) Q x =
        t.coefficient x * directionalWord F t.word f x + directionalTerms F terms f x
    rw [hQ, ih]

variable {A : Type*} [Fintype A]


def packL2 : (A → Lp ℝ 2 μ) →L[ℝ] Lp (A → ℝ) 2 μ := by
  classical
  exact ∑ a : A, ((ContinuousLinearMap.single ℝ (fun _ : A => ℝ) a).compLpL 2 μ).comp
    (ContinuousLinearMap.proj a)

theorem packL2_coe (Q : A → Lp ℝ 2 μ) :
    packL2 μ Q =ᵐ[μ] fun x a => Q a x := by
  classical
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun a : A => (ContinuousLinearMap.single ℝ (fun _ : A => ℝ) a).compLpL 2 μ (Q a)),
    ae_all_iff.mpr (fun a : A =>
      (ContinuousLinearMap.single ℝ (fun _ : A => ℝ) a).coeFn_compLpL (Q a))]
    with x hsum hsingle
  simp only [packL2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [hsum]
  ext a
  simp [hsingle, ContinuousLinearMap.single_apply]

theorem packL2_ae_eq (Q : A → Lp ℝ 2 μ) (f : A → M → ℝ)
    (hQ : ∀ a, Q a =ᵐ[μ] f a) :
    packL2 μ Q =ᵐ[μ] fun x a => f a x := by
  filter_upwards [packL2_coe μ Q, ae_all_iff.mpr hQ] with x hx h
  exact hx.trans (funext h)


def packContinuous : (A → C(M, ℝ)) →L[ℝ] C(M, A → ℝ) := by
  classical
  exact ∑ a : A,
    ((ContinuousLinearMap.single ℝ (fun _ : A => ℝ) a).compLeftContinuous ℝ M).comp
      (ContinuousLinearMap.proj a)

theorem packContinuous_apply (Q : A → C(M, ℝ)) (x : M) (a : A) :
    packContinuous Q x a = Q a x := by
  classical
  simp [packContinuous, ContinuousLinearMap.single_apply]

end CompletedTuples

end PoincareConjecture.DeTurckJetCoordinatesNative

end
