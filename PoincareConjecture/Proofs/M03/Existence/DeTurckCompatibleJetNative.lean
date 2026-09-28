import PoincareConjecture.Proofs.M03.Existence.DeTurckQuasilinearEstimateNative
import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.DeTurckCompatibleJetNative

open TensorProbeNative DeTurckNative DeTurckInverseCompositionNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_supported_chart_cutoff (p : M) {K : Set M}
    (hK : IsClosed K) (hKU : K ⊆ (chartAt E p).source) :
    ∃ eta : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ eta ∧
      (∀ x, eta x ∈ Icc 0 1) ∧ tsupport eta ⊆ (chartAt E p).source ∧
      ∀ x ∈ K, eta =ᶠ[𝓝 x] 1 := by
  have hd : Disjoint ((chartAt E p).source)ᶜ K :=
    disjoint_left.mpr (fun x hx hxK => hx (hKU hxK))
  obtain ⟨f, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡 n)
      (chartAt E p).open_source.isClosed_compl hK hd (n := (⊤ : ℕ∞))
  refine ⟨f, f.contMDiff, hbounds, ?_, ?_⟩
  · intro x hx
    by_contra hxU
    have hz : (f : M → ℝ) =ᶠ[𝓝 x] 0 := hzero.filter_mono (nhds_le_nhdsSet hxU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  · intro x hx
    exact hone.filter_mono (nhds_le_nhdsSet hx)

structure Cutoffs (p : M) (K : Set M) where
  eta : M → ℝ
  zeta : M → ℝ
  eta_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ eta
  zeta_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ zeta
  eta_bounds : ∀ x, eta x ∈ Icc 0 1
  eta_support : tsupport eta ⊆ (chartAt E p).source
  zeta_support : tsupport zeta ⊆ (chartAt E p).source
  eta_one : ∀ x ∈ K, eta =ᶠ[𝓝 x] 1
  zeta_one : ∀ x ∈ tsupport eta, zeta =ᶠ[𝓝 x] 1

theorem exists_cutoffs (p : M) {K : Set M} (hK : IsCompact K)
    (hKU : K ⊆ (chartAt E p).source) : Nonempty (Cutoffs (n := n) p K) := by
  obtain ⟨eta, heta, heta01, hetaU, heta1⟩ :=
    exists_supported_chart_cutoff p hK.isClosed hKU
  obtain ⟨zeta, hzeta, _, hzetaU, hzeta1⟩ :=
    exists_supported_chart_cutoff p (isClosed_tsupport eta) hetaU
  exact ⟨⟨eta, zeta, heta, hzeta, heta01, hetaU, hzetaU, heta1, hzeta1⟩⟩

namespace Cutoffs

variable {p : M} {K : Set M} (C : Cutoffs (n := n) p K)

def field (a : Fin n) : SmoothField (n := n) (M := M) :=
  ⟨fun x => C.zeta x • chartFrame p a x,
    C.zeta_smooth.contMDiffOn.smul_section_of_tsupport
      (chartAt E p).open_source C.zeta_support (chartFrame_contMDiffOn p a)⟩

theorem field_eventuallyEq {x : M} (hzeta : C.zeta =ᶠ[𝓝 x] 1) (a : Fin n) :
    (C.field a : (y : M) → TangentSpace (𝓡 n) y) =ᶠ[𝓝 x] chartFrame p a := by
  filter_upwards [hzeta] with y hy
  change C.zeta y • chartFrame p a y = chartFrame p a y
  simp only [hy, Pi.one_apply, one_smul]

def matrix (g : RiemannianMetric n M) : M → Matrix (Fin n) (Fin n) ℝ :=
  positiveMatrixExtension C.eta (fun x => (frameMetricJet g (chartFrame p) x).value)

theorem matrix_posDef (g : RiemannianMetric n M) (x : M) : (C.matrix g x).PosDef := by
  apply positiveMatrixExtension_posDef C.eta _
    (fun y => (C.eta_bounds y).1) (fun y => (C.eta_bounds y).2)
  intro y hy
  have hyU := C.eta_support (subset_tsupport C.eta hy)
  exact frameMetricJet_value_posDef g (chartFrame p) y
    (chartFrameBasis p y hyU) (chartFrame_eq_basis p y hyU)

theorem matrix_contMDiff (g : RiemannianMetric n M) :
    ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => C.matrix g x i j) := by
  apply positiveMatrixExtension_contMDiff C.eta _
    (chartAt E p).open_source C.eta_smooth C.eta_support
  intro i j x hx
  have hs := frameMetricJet_value_contMDiffAt g (chartFrame p) (fun a =>
    (chartFrame_contMDiffOn p a).contMDiffAt ((chartAt E p).open_source.mem_nhds hx))
  exact (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hs i) j).contMDiffWithinAt

theorem matrix_entry_contMDiff (g : RiemannianMetric n M) (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => C.matrix g x i j) :=
  fun x => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (C.matrix_contMDiff g x) i) j

def jet (g : RiemannianMetric n M) (x : M) : MetricJet2 (n := n) where
  value := C.matrix g x
  first a i j := directionalWord C.field [a] (fun y => C.matrix g y i j) x
  second a b i j := directionalWord C.field [a, b] (fun y => C.matrix g y i j) x

theorem jet_first_contMDiff (g : RiemannianMetric n M) (a i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (C.jet g x).first a i j) :=
  directionalWord_contMDiff C.field [a] (C.matrix_entry_contMDiff g i j)

theorem jet_second_contMDiff (g : RiemannianMetric n M) (a b i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (C.jet g x).second a b i j) :=
  directionalWord_contMDiff C.field [a, b] (C.matrix_entry_contMDiff g i j)

theorem matrix_symm (g : RiemannianMetric n M) (x : M) (i j : Fin n) :
    C.matrix g x i j = C.matrix g x j i := by
  change C.eta x * g.inner x (chartFrame p i x) (chartFrame p j x) +
      (1 - C.eta x) * (1 : Matrix (Fin n) (Fin n) ℝ) i j =
    C.eta x * g.inner x (chartFrame p j x) (chartFrame p i x) +
      (1 - C.eta x) * (1 : Matrix (Fin n) (Fin n) ℝ) j i
  rw [g.symm x (chartFrame p i x) (chartFrame p j x)]
  simp only [Matrix.one_apply, eq_comm]

theorem jet_first_symm (g : RiemannianMetric n M) (x : M) (a i j : Fin n) :
    (C.jet g x).first a i j = (C.jet g x).first a j i :=
  congrArg (fun f : M → ℝ => directionalWord C.field [a] f x)
    (funext (fun y => C.matrix_symm g y i j))

theorem jet_second_symm (g : RiemannianMetric n M) (x : M) (a b i j : Fin n) :
    (C.jet g x).second a b i j = (C.jet g x).second a b j i :=
  congrArg (fun f : M → ℝ => directionalWord C.field [a, b] f x)
    (funext (fun y => C.matrix_symm g y i j))

theorem matrix_eventuallyEq_of_notMem (g : RiemannianMetric n M) {x : M}
    (hx : x ∉ tsupport C.eta) : C.matrix g =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [matrix, positiveMatrixExtension, hy, Pi.zero_apply, zero_smul,
    sub_zero, one_smul, zero_add]

theorem jet_second_swap (g : RiemannianMetric n M) (x : M) (a b i j : Fin n) :
    (C.jet g x).second a b i j = (C.jet g x).second b a i j := by
  by_cases hx : x ∈ tsupport C.eta
  · have ha := C.field_eventuallyEq (C.zeta_one x hx) a
    have hb := C.field_eventuallyEq (C.zeta_one x hx) b
    have hbracket : smoothFieldBracket (C.field a) (C.field b) x = 0 := by
      change VectorField.mlieBracket (𝓡 n) (C.field a) (C.field b) x = 0
      rw [ha.mlieBracket_vectorField_eq hb]
      exact chartFrame_mlieBracket_eq_zero p x (C.eta_support hx) a b
    have h := scalarDirectional_bracket (C.field a) (C.field b)
      (C.matrix_entry_contMDiff g i j) x
    have hzero : scalarDirectional (smoothFieldBracket (C.field a) (C.field b))
        (fun y => C.matrix g y i j) x = 0 := by
      simp only [scalarDirectional, hbracket, map_zero]
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  · have hconst : (fun y => C.matrix g y i j) =ᶠ[𝓝 x]
        fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      filter_upwards [C.matrix_eventuallyEq_of_notMem g hx] with y hy
      rw [hy]
    have hab := (directionalWord_eventuallyEq C.field [a, b] hconst).eq_of_nhds
    have hba := (directionalWord_eventuallyEq C.field [b, a] hconst).eq_of_nhds
    change directionalWord C.field [a, b] (fun y => C.matrix g y i j) x =
      directionalWord C.field [b, a] (fun y => C.matrix g y i j) x
    rw [hab, hba]
    have hD (k : Fin n) :
        scalarDirectional (C.field k) (fun _ : M => (1 : Matrix (Fin n) (Fin n) ℝ) i j) =
          fun _ => 0 := by
      funext y
      simp only [scalarDirectional, mfderiv_const]
      rfl
    simp only [directionalWord_cons, directionalWord_nil, hD]
    simp only [scalarDirectional, mfderiv_const]
    rfl

theorem matrix_eventuallyEq (g : RiemannianMetric n M) {x : M}
    (heta : C.eta =ᶠ[𝓝 x] 1) : C.matrix g =ᶠ[𝓝 x]
      fun y => (frameMetricJet g (chartFrame p) y).value :=
  positiveMatrixExtension_eventuallyEq C.eta _ heta

theorem jet_first_eventuallyEq (g : RiemannianMetric n M) {x : M}
    (heta : C.eta =ᶠ[𝓝 x] 1) (hzeta : C.zeta =ᶠ[𝓝 x] 1) (a i j : Fin n) :
    (fun y => (C.jet g y).first a i j) =ᶠ[𝓝 x]
      fun y => (frameMetricJet g (chartFrame p) y).first a i j := by
  have hv : (fun y => C.matrix g y i j) =ᶠ[𝓝 x]
      fun y => (frameMetricJet g (chartFrame p) y).value i j := by
    filter_upwards [C.matrix_eventuallyEq g heta] with y hy
    rw [hy]
  filter_upwards [hv.eventuallyEq_nhds, C.field_eventuallyEq hzeta a] with y hy hfield
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun z => C.matrix g z i j) y (C.field a y) = _
  rw [hy.mfderiv_eq, hfield]
  rfl

theorem jet_eq (g : RiemannianMetric n M) {x : M}
    (heta : C.eta =ᶠ[𝓝 x] 1) (hzeta : C.zeta =ᶠ[𝓝 x] 1) :
    C.jet g x = frameMetricJet g (chartFrame p) x := by
  have hvalue := (C.matrix_eventuallyEq g heta).eq_of_nhds
  have hfirst : (C.jet g x).first = (frameMetricJet g (chartFrame p) x).first := by
    funext a i j
    exact (C.jet_first_eventuallyEq g heta hzeta a i j).eq_of_nhds
  have hsecond : (C.jet g x).second = (frameMetricJet g (chartFrame p) x).second := by
    funext a b i j
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => (C.jet g y).first b i j) x (C.field a x) = _
    rw [(C.jet_first_eventuallyEq g heta hzeta b i j).mfderiv_eq,
      (C.field_eventuallyEq hzeta a).eq_of_nhds]
    rfl
  change MetricJet2.mk (C.matrix g x) (C.jet g x).first (C.jet g x).second =
    MetricJet2.mk (frameMetricJet g (chartFrame p) x).value
      (frameMetricJet g (chartFrame p) x).first (frameMetricJet g (chartFrame p) x).second
  rw [hvalue, hfirst, hsecond]

theorem mem_eta_support {x : M} (hx : x ∈ K) : x ∈ tsupport C.eta := by
  apply subset_tsupport C.eta
  change C.eta x ≠ 0
  have heta : C.eta x = 1 := (C.eta_one x hx).eq_of_nhds
  rw [heta]
  exact one_ne_zero

theorem jet_eq_on (g : RiemannianMetric n M) {x : M} (hx : x ∈ K) :
    C.jet g x = frameMetricJet g (chartFrame p) x := by
  have heta := C.eta_one x hx
  exact C.jet_eq g heta (C.zeta_one x (C.mem_eta_support hx))

theorem jet_difference (g h : RiemannianMetric n M) (x : M) (i j : Fin n)
    (w : List (Fin n)) :
    directionalWord C.field w (fun y => C.matrix g y i j - C.matrix h y i j) x =
      directionalWord C.field w (fun y => C.eta y *
        (g.inner y (chartFrame p i y) (chartFrame p j y) -
          h.inner y (chartFrame p i y) (chartFrame p j y))) x := by
  congr 1
  funext y
  have heq := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
    (positiveMatrixExtension_sub C.eta
      (fun z => (frameMetricJet g (chartFrame p) z).value)
      (fun z => (frameMetricJet h (chartFrame p) z).value) y)
  exact heq

def lowerDifference (g0 g : RiemannianMetric n M) (x : M) : MetricLowerJet n :=
  backgroundLowerJet (C.jet g x) - backgroundLowerJet (C.jet g0 x)

def secondDifference (g0 g : RiemannianMetric n M) (x : M) : MetricSecondJet n :=
  (C.jet g x).second - (C.jet g0 x).second

def residual (g0 g : RiemannianMetric n M) (x : M) : Matrix (Fin n) (Fin n) ℝ :=
  perturbationRemainder (C.jet g0 x) (C.lowerDifference g0 g x) (C.secondDifference g0 g x)

theorem residual_eq_source (g0 g : RiemannianMetric n M) (x : M) (i j : Fin n) :
    C.residual g0 g x i j = ricciDeTurckSource (C.jet g0 x) (C.jet g x) i j -
      lowerJetContraction (C.jet g0 x).value⁻¹ (C.secondDifference g0 g x) i j := by
  have hp : backgroundLowerJet (C.jet g0 x) + C.lowerDifference g0 g x =
      backgroundLowerJet (C.jet g x) := by dsimp only [lowerDifference]; abel
  have hq : (C.jet g0 x).second + C.secondDifference g0 g x = (C.jet g x).second := by
    dsimp only [secondDifference]
    abel
  unfold residual perturbationRemainder
  rw [hp, hq]
  simp only [chartStateSource,
    lowerJetState, chartStateJet, backgroundLowerJet]

theorem residual_eq_intrinsic (g0 g : RiemannianMetric n M)
    (B : LeviCivitaData g0) (D : LeviCivitaData g) {x : M} (hx : x ∈ K) (i j : Fin n) :
    C.residual g0 g x i j =
      -2 * D.ricci x (chartFrame p i x) (chartFrame p j x) +
        metricLieDerivative D (intrinsicDeTurckField D B) x
          (chartFrame p i x) (chartFrame p j x) -
        lowerJetContraction (C.jet g0 x).value⁻¹ (C.secondDifference g0 g x) i j := by
  rw [C.residual_eq_source g0 g x i j]
  congr 1
  rw [C.jet_eq_on g0 hx, C.jet_eq_on g hx]
  exact ricciDeTurckSource_frameMetricJet_eq_intrinsic D B p
    (C.eta_support (C.mem_eta_support hx)) i j

section NativeCoordinates

variable {iota : Type*} [Fintype iota]

def fieldCoefficient (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (a : Fin n) (i : iota) (x : M) : ℝ :=
  g0.inner x (F i x) (C.field a x)

theorem fieldCoefficient_contMDiff (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (a : Fin n) (i : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C.fieldCoefficient g0 F a i) :=
  contMDiff_pairing (metricTensor g0) (F i) (C.field a)

theorem field_eq_sum (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v) (a : Fin n) (x : M) :
    C.field a x = ∑ i, C.fieldCoefficient g0 F a i x • F i x :=
  (hF x (C.field a x)).symm

theorem jet_first_eq_native (g0 g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v) (x : M) (a i j : Fin n) :
    (C.jet g x).first a i j = ∑ q,
      C.fieldCoefficient g0 F a q x * scalarDirectional (F q) (fun y => C.matrix g y i j) x := by
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => C.matrix g y i j) x (C.field a x) = _
  rw [C.field_eq_sum g0 F hF a x, map_sum]
  simp only [map_smul, smul_eq_mul, scalarDirectional]

theorem jet_second_eq_native (g0 g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g0.inner x (F i x) v • F i x) = v) (x : M) (a b i j : Fin n) :
    (C.jet g x).second a b i j =
      (∑ q, ∑ r, C.fieldCoefficient g0 F a q x * C.fieldCoefficient g0 F b r x *
        directionalWord F [q, r] (fun y => C.matrix g y i j) x) +
      ∑ q, ∑ r, C.fieldCoefficient g0 F a q x *
        scalarDirectional (F q) (C.fieldCoefficient g0 F b r) x *
        scalarDirectional (F r) (fun y => C.matrix g y i j) x := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact DeTurckQuasilinearEstimateNative.second_derivative_eq_of_field_sum
    F (fun a => C.field a) (C.fieldCoefficient g0 F) isOpen_univ
    (fun a q => (C.fieldCoefficient_contMDiff g0 F a q).contMDiffOn)
    (fun a y _ => C.field_eq_sum g0 F hF a y)
    (C.matrix_entry_contMDiff g i j) a b (mem_univ x)

def probeCoefficient (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (i j : Fin n) (a b : iota) (x : M) : ℝ :=
  C.eta x * C.fieldCoefficient g0 F i a x * C.fieldCoefficient g0 F j b x

theorem probeCoefficient_contMDiff (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (i j : Fin n) (a b : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C.probeCoefficient g0 F i j a b) :=
  (C.eta_smooth.mul (C.fieldCoefficient_contMDiff g0 F i a)).mul
    (C.fieldCoefficient_contMDiff g0 F j b)

theorem matrix_sub_eq_sum_probes (g0 g h : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v) (x : M) (i j : Fin n) :
    C.matrix g x i j - C.matrix h x i j =
      ∑ a, ∑ b, C.probeCoefficient g0 F i j a b x *
        (g.inner x (F a x) (F b x) - h.inner x (F a x) (F b x)) := by
  have hmatrix : C.matrix g x i j - C.matrix h x i j =
      C.eta x * (g.inner x (C.field i x) (C.field j x) -
        h.inner x (C.field i x) (C.field j x)) := by
    have hsub := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
      (positiveMatrixExtension_sub C.eta
        (fun y => (frameMetricJet g (chartFrame p) y).value)
        (fun y => (frameMetricJet h (chartFrame p) y).value) x)
    change C.matrix g x i j - C.matrix h x i j =
      C.eta x * (g.inner x (chartFrame p i x) (chartFrame p j x) -
        h.inner x (chartFrame p i x) (chartFrame p j x)) at hsub
    rw [hsub]
    by_cases hx : C.eta x = 0
    · simp only [hx, zero_mul]
    · have hs : x ∈ tsupport C.eta := subset_tsupport C.eta hx
      rw [(C.field_eventuallyEq (C.zeta_one x hs) i).eq_of_nhds,
        (C.field_eventuallyEq (C.zeta_one x hs) j).eq_of_nhds]
  have hpair (k : RiemannianMetric n M) :
      k.inner x (C.field i x) (C.field j x) =
        ∑ a, ∑ b, C.fieldCoefficient g0 F i a x * C.fieldCoefficient g0 F j b x *
          k.inner x (F a x) (F b x) := by
    rw [C.field_eq_sum g0 F hF i x, C.field_eq_sum g0 F hF j x]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hmatrix, hpair g, hpair h, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [probeCoefficient]
  ring

theorem directionalWord_matrix_sub (g h : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) (i j : Fin n) :
    directionalWord F w (fun x => C.matrix g x i j - C.matrix h x i j) =
      fun x => directionalWord F w (fun y => C.matrix g y i j) x -
        directionalWord F w (fun y => C.matrix h y i j) x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    funext x
    rw [directionalWord_cons, ih]
    exact scalarDirectional_sub (F a)
      ((directionalWord_contMDiff F w (C.matrix_entry_contMDiff g i j)).mdifferentiable
        (by simp) x)
      ((directionalWord_contMDiff F w (C.matrix_entry_contMDiff h i j)).mdifferentiable
        (by simp) x)

section FixedCoefficientBounds

open MeasureTheory DeTurckQuasilinearEstimateNative

variable [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [IsFiniteMeasure μ]

private theorem exists_compact_scalar_family_bounds
    {gamma : Type*} [Fintype gamma]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (f : gamma → M → ℝ)
    (hf : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j, ScalarDerivativeBounds μ F r A (f j) := by
  classical
  let Index := gamma × (Σ s : Fin (2 * r + 1), Fin s.val → iota)
  let d : Index → M → ℝ := fun j => directionalWord F (List.ofFn j.2.2) (f j.1)
  have hex (j : Index) : ∃ b : ℝ, ∀ x, ‖d j x‖ ≤ b := by
    obtain ⟨b, hb⟩ := isCompact_univ.bddAbove_image
      (directionalWord_contMDiff F (List.ofFn j.2.2) (hf j.1)).continuous.norm.continuousOn
    exact ⟨b, fun x => hb ⟨x, mem_univ x, rfl⟩⟩
  choose b hb using hex
  let B : Index → ℝ := fun j => max (b j) 0 + lpNorm (d j) 2 μ
  have hB (j : Index) : 0 ≤ B j := add_nonneg (le_max_right _ _) lpNorm_nonneg
  let A : ℝ := ∑ j : Index, B j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => hB j)
  have hsum (j : Index) : B j ≤ A :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)
  have hbound (j : Index) (x : M) : ‖d j x‖ ≤ A :=
    (hb j x).trans ((le_max_left _ _).trans
      ((le_add_of_nonneg_right lpNorm_nonneg).trans (hsum j)))
  have hlp (j : Index) : lpNorm (d j) 2 μ ≤ A :=
    (le_add_of_nonneg_left (le_max_right (b j) 0)).trans (hsum j)
  refine ⟨A, hA, fun j => ⟨hA, hf j, ?_, ?_⟩⟩
  · intro w hw x
    let k : Index := (j, ⟨⟨w.length, by omega⟩, w.get⟩)
    simpa only [d, k, List.ofFn_get] using hbound k x
  · intro w hw
    let k : Index := (j, ⟨⟨w.length, by omega⟩, w.get⟩)
    simpa only [d, k, List.ofFn_get] using hlp k

theorem exists_fieldCoefficient_bounds (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ (a : Fin n) (i : iota),
        ScalarDerivativeBounds μ F r A (C.fieldCoefficient g0 F a i)) ∧
      (∀ (a : Fin n) (i j : iota),
        ScalarDerivativeBounds μ F r A
          (scalarDirectional (F i) (C.fieldCoefficient g0 F a j))) := by
  let J := (Fin n × iota) ⊕ (Fin n × iota × iota)
  let f : J → M → ℝ
    | Sum.inl ai => C.fieldCoefficient g0 F ai.1 ai.2
    | Sum.inr aij => scalarDirectional (F aij.2.1) (C.fieldCoefficient g0 F aij.1 aij.2.2)
  have hf (j : J) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) := by
    cases j with
    | inl ai => exact C.fieldCoefficient_contMDiff g0 F ai.1 ai.2
    | inr aij =>
      exact contMDiff_directional (C.fieldCoefficient_contMDiff g0 F aij.1 aij.2.2) (F aij.2.1)
  obtain ⟨A, hA, hbound⟩ := exists_compact_scalar_family_bounds μ F r f hf
  exact ⟨A, hA, fun a i => hbound (Sum.inl (a, i)),
    fun a i j => hbound (Sum.inr (a, i, j))⟩

theorem exists_probeCoefficient_bounds (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (i j : Fin n) (a b : iota),
      ScalarDerivativeBounds μ F r A (C.probeCoefficient g0 F i j a b) := by
  let J := (Fin n × Fin n) × (iota × iota)
  let f : J → M → ℝ := fun q => C.probeCoefficient g0 F q.1.1 q.1.2 q.2.1 q.2.2
  obtain ⟨A, hA, hb⟩ := exists_compact_scalar_family_bounds μ F r f
    (fun q => C.probeCoefficient_contMDiff g0 F q.1.1 q.1.2 q.2.1 q.2.2)
  exact ⟨A, hA, fun i j a b => hb ((i, j), (a, b))⟩

private theorem scalarDerivativeBounds_fintypeSum {gamma : Type*} [Fintype gamma]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (A : ℝ)
    (f : gamma → M → ℝ) (hf : ∀ a, ScalarDerivativeBounds μ F r A (f a)) :
    ScalarDerivativeBounds μ F r ((Fintype.card gamma : ℝ) * A)
      (fun x => ∑ a, f a x) := by
  let e := Fintype.equivFin gamma
  have hs := ScalarDerivativeBounds.finSum (μ := μ) (F := F) (r := r)
    (fun a => f (e.symm a)) (fun a => hf (e.symm a))
  have heq : (fun x => ∑ a : Fin (Fintype.card gamma), f (e.symm a) x) =
      fun x => ∑ a, f a x := by
    funext x
    exact e.symm.sum_comp (fun a => f a x)
  rwa [heq] at hs

theorem exists_matrixDifference_bound (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v) (r : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (g h : RiemannianMetric n M) (D : ℝ),
      (∀ a b : iota, ScalarDerivativeBounds μ F r D
        (fun x => g.inner x (F a x) (F b x) - h.inner x (F a x) (F b x))) →
      ∀ i j : Fin n, ScalarDerivativeBounds μ F r (L * D)
        (fun x => C.matrix g x i j - C.matrix h x i j) := by
  obtain ⟨A, hA, hcoeff⟩ := C.exists_probeCoefficient_bounds μ g0 F r
  let L := (Fintype.card iota : ℝ) *
    ((Fintype.card iota : ℝ) * ((2 : ℝ) ^ (2 * r + 1) * A))
  refine ⟨L, by dsimp only [L]; positivity, ?_⟩
  intro g h D hD i j
  let f : iota → iota → M → ℝ := fun a b x => C.probeCoefficient g0 F i j a b x *
    (g.inner x (F a x) (F b x) - h.inner x (F a x) (F b x))
  have hs := scalarDerivativeBounds_fintypeSum μ F r
    ((Fintype.card iota : ℝ) * ((2 : ℝ) ^ (2 * r + 1) * A * D))
    (fun a x => ∑ b, f a b x) (fun a =>
      scalarDerivativeBounds_fintypeSum μ F r ((2 : ℝ) ^ (2 * r + 1) * A * D)
        (f a) (fun b => (hcoeff i j a b).mul (hD a b)))
  have hbudget : (Fintype.card iota : ℝ) *
      ((Fintype.card iota : ℝ) * ((2 : ℝ) ^ (2 * r + 1) * A * D)) = L * D := by
    dsimp only [L]
    ring
  rw [hbudget] at hs
  have heq : (fun x => C.matrix g x i j - C.matrix h x i j) =
      fun x => ∑ a, ∑ b, f a b x := funext (fun x =>
        C.matrix_sub_eq_sum_probes g0 g h F hF x i j)
  rwa [← heq] at hs

include μ in

theorem exists_matrixDifference_low_bound (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v) (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (g h : RiemannianMetric n M) (D : ℝ), 0 ≤ D →
      (∀ w : List iota, w.length ≤ k → ∀ (a b : iota) (x : M),
        ‖directionalWord F w (fun y =>
          g.inner y (F a y) (F b y) - h.inner y (F a y) (F b y)) x‖ ≤ D) →
      ∀ w : List iota, w.length ≤ k → ∀ (i j : Fin n) (x : M),
        ‖directionalWord F w (fun y => C.matrix g y i j - C.matrix h y i j) x‖ ≤ L * D := by
  obtain ⟨A, hA, hcoeff⟩ := C.exists_probeCoefficient_bounds μ g0 F k
  let L := (Fintype.card iota : ℝ) ^ 2 * (2 : ℝ) ^ k * A
  refine ⟨L, by dsimp only [L]; positivity, ?_⟩
  intro g h D hD hprobe w hw i j x
  let f : iota → iota → M → ℝ := fun a b y => C.probeCoefficient g0 F i j a b y *
    (g.inner y (F a y) (F b y) - h.inner y (F a y) (F b y))
  have hprobeSmooth (a b : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (F a y) (F b y) - h.inner y (F a y) (F b y)) :=
    (contMDiff_pairing (metricTensor g) (F a) (F b)).sub
      (contMDiff_pairing (metricTensor h) (F a) (F b))
  have hf (a b : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a b) :=
    (hcoeff i j a b).smooth.mul (hprobeSmooth a b)
  have hs (a : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ∑ b, f a b y) :=
    ContMDiff.sum (t := Finset.univ) (fun b _ => hf a b)
  have heq : (fun y => C.matrix g y i j - C.matrix h y i j) =
      fun y => ∑ a, ∑ b, f a b y := funext (fun y =>
        C.matrix_sub_eq_sum_probes g0 g h F hF y i j)
  have hword : directionalWord F w (fun y => C.matrix g y i j - C.matrix h y i j) x =
      ∑ a, ∑ b, directionalWord F w (f a b) x := by
    rw [heq, directionalWord_sum Finset.univ F w _ (fun a _ => hs a)]
    apply Finset.sum_congr rfl
    intro a _
    exact directionalWord_sum Finset.univ F w _ (fun b _ => hf a b) x
  have hterm (a b : iota) :
      ‖directionalWord F w (f a b) x‖ ≤ (2 : ℝ) ^ k * A * D :=
    norm_directionalWord_mul_le F k w hw (hcoeff i j a b).smooth
      (hprobeSmooth a b) hA hD (hcoeff i j a b).low
      (fun z hz y => hprobe z hz a b y) x
  rw [hword]
  calc
    _ ≤ ∑ a : iota, ∑ b : iota, ‖directionalWord F w (f a b) x‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : iota, ∑ _b : iota, (2 : ℝ) ^ k * A * D :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))
    _ = L * D := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, L]; ring

theorem exists_background_matrix_bounds (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i j : Fin n,
      ScalarDerivativeBounds μ F (r + 1) A (fun x => C.matrix g0 x i j) := by
  obtain ⟨A, hA, hb⟩ := exists_compact_scalar_family_bounds μ F (r + 1)
    (fun q : Fin n × Fin n => fun x => C.matrix g0 x q.1 q.2)
    (fun q => C.matrix_entry_contMDiff g0 q.1 q.2)
  exact ⟨A, hA, fun i j => hb (i, j)⟩

section UniformInverse

open scoped Matrix.Norms.Elementwise

theorem exists_matrix_inverse_radius (g0 : RiemannianMetric n M) :
    ∃ rho I : ℝ, 0 < rho ∧ 0 < I ∧
      ∀ g : RiemannianMetric n M,
        (∀ (i j : Fin n) (x : M), ‖C.matrix g x i j - C.matrix g0 x i j‖ ≤ rho) →
        ∀ (i j : Fin n) (x : M), ‖(C.matrix g x)⁻¹ i j‖ ≤ I := by
  obtain ⟨rho, I, hrho, hI, hbound⟩ := exists_uniform_inverse_perturbation
    (C.matrix g0) (C.matrix_contMDiff g0).continuous (C.matrix_posDef g0)
  refine ⟨rho, I, hrho, hI, ?_⟩
  intro g hg i j x
  have hs (y : M) : (C.matrix g y - C.matrix g0 y).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    change C.matrix g y b a - C.matrix g0 y b a =
      C.matrix g y a b - C.matrix g0 y a b
    rw [C.matrix_symm g y b a, C.matrix_symm g0 y b a]
  have hn (y : M) : ‖C.matrix g y - C.matrix g0 y‖ ≤ rho :=
    (Matrix.norm_le_iff hrho.le).mpr (fun a b => hg a b y)
  have hsum : C.matrix g0 x + (C.matrix g x - C.matrix g0 x) = C.matrix g x := by abel
  simpa only [hsum] using (hbound (fun y => C.matrix g y - C.matrix g0 y) hs hn x).2 i j

end UniformInverse

theorem exists_uniform_matrixDerivative_bounds (g0 : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v) (r : ℕ) :
    ∃ rho A I : ℝ, 0 < rho ∧ 0 ≤ A ∧ 0 < I ∧
      ∀ g : RiemannianMetric n M,
        (∀ w : List iota, w.length ≤ r + 1 → ∀ (a b : iota) (x : M),
          ‖directionalWord F w (fun y =>
            g.inner y (F a y) (F b y) - g0.inner y (F a y) (F b y)) x‖ ≤ rho) →
        (∀ w : List iota, w.length ≤ 2 * r → ∀ a b : iota,
          lpNorm (directionalWord F w (fun y =>
            g.inner y (F a y) (F b y) - g0.inner y (F a y) (F b y))) 2 μ ≤ rho) →
        (∀ w : List iota, w.length ≤ r + 1 → ∀ (i j : Fin n) (x : M),
          ‖directionalWord F w (fun y => C.matrix g y i j) x‖ ≤ A) ∧
        (∀ (i j : Fin n) (x : M), ‖(C.matrix g x)⁻¹ i j‖ ≤ I) ∧
        (∀ w : List iota, w.length ≤ 2 * r → ∀ i j : Fin n,
          lpNorm (directionalWord F w (fun y => C.matrix g y i j)) 2 μ ≤ A) := by
  obtain ⟨L0, hL0, hhigh⟩ := C.exists_matrixDifference_bound μ g0 F hF r
  obtain ⟨L1, hL1, hlow⟩ := C.exists_matrixDifference_low_bound μ g0 F hF (r + 1)
  obtain ⟨A0, hA0, hbackground⟩ := C.exists_background_matrix_bounds μ g0 F r
  obtain ⟨rho0, I, hrho0, hI, hinverse⟩ := C.exists_matrix_inverse_radius g0
  let B := max L1 L0 + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [le_max_left L1 L0]
  have hL0B : L0 ≤ B :=
    (le_max_right L1 L0).trans (le_add_of_nonneg_right zero_le_one)
  have hL1B : L1 ≤ B :=
    (le_max_left L1 L0).trans (le_add_of_nonneg_right zero_le_one)
  let rho := min 1 (rho0 / B)
  have hrho : 0 < rho := lt_min one_pos (div_pos hrho0 hB)
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hrhoB : rho * B ≤ rho0 := (le_div_iff₀ hB).mp (min_le_right _ _)
  have hL0rho : L0 * rho ≤ B :=
    (mul_le_mul_of_nonneg_right hL0B hrho.le).trans
      (mul_le_of_le_one_right hB.le hrho1)
  have hL1rho : L1 * rho ≤ B :=
    (mul_le_mul_of_nonneg_right hL1B hrho.le).trans
      (mul_le_of_le_one_right hB.le hrho1)
  have hsmall : L1 * rho ≤ rho0 :=
    (mul_le_mul_of_nonneg_right hL1B hrho.le).trans
      (by simpa only [mul_comm] using hrhoB)
  refine ⟨rho, A0 + B, I, hrho, add_nonneg hA0 hB.le, hI, ?_⟩
  intro g hprobeLow hprobeHigh
  have hprobe (a b : iota) : ScalarDerivativeBounds μ F r rho
      (fun y => g.inner y (F a y) (F b y) - g0.inner y (F a y) (F b y)) := by
    refine ⟨hrho.le,
      (contMDiff_pairing (metricTensor g) (F a) (F b)).sub
        (contMDiff_pairing (metricTensor g0) (F a) (F b)), ?_, ?_⟩
    · intro w hw x
      exact hprobeLow w (by omega) a b x
    · intro w hw
      exact hprobeHigh w hw a b
  have hdifference := hhigh g g0 rho hprobe
  have hlowDifference := hlow g g0 rho hrho.le hprobeLow
  refine ⟨?_, ?_, ?_⟩
  · intro w hw i j x
    have hbase := (hbackground i j).low w hw x
    have hdiff := hlowDifference w hw i j x
    rw [C.directionalWord_matrix_sub g g0 F w i j] at hdiff
    calc
      _ = ‖directionalWord F w (fun y => C.matrix g0 y i j) x +
          (directionalWord F w (fun y => C.matrix g y i j) x -
            directionalWord F w (fun y => C.matrix g0 y i j) x)‖ := by
        congr 1
        ring
      _ ≤ ‖directionalWord F w (fun y => C.matrix g0 y i j) x‖ +
          ‖directionalWord F w (fun y => C.matrix g y i j) x -
            directionalWord F w (fun y => C.matrix g0 y i j) x‖ := norm_add_le _ _
      _ ≤ A0 + L1 * rho := add_le_add hbase hdiff
      _ ≤ A0 + B := add_le_add le_rfl hL1rho
  · apply hinverse g
    intro i j x
    exact (hlowDifference [] (by simp) i j x).trans hsmall
  · intro w hw i j
    have hbase : ScalarDerivativeBounds μ F r A0 (fun y => C.matrix g0 y i j) := by
      refine ⟨hA0, (hbackground i j).smooth, ?_, ?_⟩
      · intro z hz x
        exact (hbackground i j).low z (by omega) x
      · intro z hz
        exact (hbackground i j).high z (by omega)
    have hsum := hbase.add (hdifference i j)
    have heq : (fun y => C.matrix g0 y i j + (C.matrix g y i j - C.matrix g0 y i j)) =
        fun y => C.matrix g y i j := by
      funext y
      ring
    rw [heq] at hsum
    exact (hsum.high w hw).trans (add_le_add le_rfl hL0rho)

end FixedCoefficientBounds

end NativeCoordinates

end Cutoffs

end PoincareConjecture.DeTurckCompatibleJetNative
