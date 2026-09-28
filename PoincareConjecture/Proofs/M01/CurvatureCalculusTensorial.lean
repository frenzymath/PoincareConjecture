import PoincareConjecture.Proofs.M01.CurvatureCalculusFields
import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring










set_option autoImplicit false
open scoped Manifold ContDiff Bundle
open Bundle Module

namespace PoincareConjecture

def SmoothTensorialOn
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [(x : M) → AddCommGroup (V x)] [(x : M) → Module 𝕜 (V x)]
    [(x : M) → TopologicalSpace (V x)] [FiberBundle F V]
    {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    (Φ : (∀ x : M, V x) → A) (x : M) : Prop :=
  (∀ {U : Set M}, IsOpen U → x ∈ U →
    ∀ {σ τ : ∀ x : M, V x},
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% σ) U →
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% τ) U →
    (∀ y ∈ U, σ y = τ y) → Φ σ = Φ τ) ∧
  (∀ {U : Set M}, IsOpen U → x ∈ U →
    ∀ {f : M → 𝕜} {σ : ∀ x : M, V x},
    ContMDiffOn I 𝓘(𝕜, 𝕜) ∞ f U →
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% σ) U → Φ (f • σ) = f x • Φ σ) ∧
  (∀ {U : Set M}, IsOpen U → x ∈ U →
    ∀ {σ τ : ∀ x : M, V x},
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% σ) U →
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% τ) U → Φ (σ + τ) = Φ σ + Φ τ)

namespace SmoothTensorialOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [(x : M) → AddCommGroup (V x)] [(x : M) → Module 𝕜 (V x)]
    [(x : M) → TopologicalSpace (V x)] [FiberBundle F V]
    {A : Type*} [AddCommGroup A] [Module 𝕜 A]
    {Φ : (∀ x : M, V x) → A} {x : M}

theorem pointwise
    [VectorBundle 𝕜 F V] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle ∞ F V I]
    (hΦ : SmoothTensorialOn (I := I) (F := F) Φ x)
    {U : Set M} (hU : IsOpen U) (hx : x ∈ U)
    {σ σ' : ∀ x : M, V x}
    (hσ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% σ) U)
    (hσ' : ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% σ') U)
    (hσσ' : σ x = σ' x) : Φ σ = Φ σ' := by
  let e := trivializationAt F V x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let W := U ∩ e.baseSet
  have hW : IsOpen W := hU.inter e.open_baseSet
  have hxW : x ∈ W := ⟨hx, hxe⟩
  let b := Module.Basis.ofVectorSpace 𝕜 F
  let s := e.localFrame b
  let c := e.localFrameCoeff I b
  have hs (i) : ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% (s i)) W := by
    exact (e.contMDiffOn_localFrame_baseSet ∞ b i).mono Set.inter_subset_right
  have hc {τ : ∀ x : M, V x}
      (hτ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% τ) U) (i) :
      ContMDiffOn I 𝓘(𝕜, 𝕜) ∞ (LinearMap.piApply (c i) τ) W := by
    exact contMDiffOn_localFrameCoeff b hW Set.inter_subset_right
      (hτ.mono Set.inter_subset_left) i
  let expand (τ : ∀ x : M, V x) : ∀ x : M, V x :=
    fun y ↦ ∑ i, (c i y) (τ y) • s i y
  have heq {τ : ∀ x : M, V x}
      (hτ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% τ) U) : Φ τ = Φ (expand τ) := by
    apply hΦ.1 hW hxW
    · exact hτ.mono Set.inter_subset_left
    · simpa [expand] using (ContMDiffOn.sum_section
        (fun i _ ↦ (hc hτ i).smul_section (hs i)))
    · intro y hy
      exact e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := τ) hy.2
  have hsum {τ : ∀ x : M, V x}
      (hτ : ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞ (T% τ) U) :
      Φ (expand τ) = ∑ i, Φ ((LinearMap.piApply (c i) τ) • (s i)) := by
    classical
    let hterm : ∀ i : Module.Basis.ofVectorSpaceIndex 𝕜 F,
        ContMDiffOn I (I.prod 𝓘(𝕜, F)) ∞
          (T% ((LinearMap.piApply (c i) τ) • (s i))) W :=
      fun i ↦ (hc hτ i).smul_section (hs i)
    have hzero : Φ (fun y : M ↦ (0 : V y)) = 0 := by
      have hz := hΦ.2.1 hW hxW (f := fun _ : M ↦ (0 : 𝕜))
        contMDiffOn_const (contMDiffOn_zeroSection 𝕜 V)
      have hzero_fun : (fun _ : M ↦ (0 : 𝕜)) • (fun y : M ↦ (0 : V y)) =
          (fun y : M ↦ (0 : V y)) := by
        funext y
        exact zero_smul 𝕜 (0 : V y)
      rw [hzero_fun] at hz
      simpa only [zero_smul] using hz
    have hsum' : ∀ (t : Finset (Module.Basis.ofVectorSpaceIndex 𝕜 F)),
        Φ (fun y ↦ ∑ i ∈ t, ((LinearMap.piApply (c i) τ) • (s i)) y) =
          ∑ i ∈ t, Φ ((LinearMap.piApply (c i) τ) • (s i)) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using hzero
      | @insert i t hi ih =>
          simp only [Finset.sum_insert hi, ← ih]
          exact hΦ.2.2 hW hxW (hterm i)
            (ContMDiffOn.sum_section (s := t) (fun j _ ↦ hterm j))
    simpa [expand] using hsum' (Finset.univ : Finset (Module.Basis.ofVectorSpaceIndex 𝕜 F))
  rw [heq hσ, heq hσ', hsum hσ, hsum hσ']
  congr 1
  funext i
  have hci : (c i x) (σ x) = (c i x) (σ' x) := by rw [hσσ']
  calc
    Φ ((LinearMap.piApply (c i) σ) • (s i)) =
        (c i x) (σ x) • Φ (s i) := hΦ.2.1 hW hxW (hc hσ i) (hs i)
    _ = (c i x) (σ' x) • Φ (s i) := by rw [hci]
    _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
      (hΦ.2.1 hW hxW (hc hσ' i) (hs i)).symm

end SmoothTensorialOn

open Filter

namespace LeviCivitaData

open scoped Manifold ContDiff Bundle

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

abbrev Vec (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :=
  (x : M) → TangentSpace (𝓡 n) x

abbrev VecSmooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (U : Set M) (X : Vec n M) :=
  ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U

private theorem tensorial_left (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    {x : M} (hx : x ∈ U) {Y Z : Vec n M}
    (hY : VecSmooth U Y) (hZ : VecSmooth U Z) :
    SmoothTensorialOn (I := 𝓡 n) (F := EuclideanSpace ℝ (Fin n))
      (fun X ↦ D.curvatureOnFields X Y Z x) x := by
  refine ⟨?_, ?_, ?_⟩
  · intro V hV hxV X X' hX hX' hXX'
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    have hxS : x ∈ S := ⟨hxV, hx⟩
    exact D.curvatureOnFields_congr_of_eqOn hS X X' Y Y Z Z
      (hX.mono Set.inter_subset_left) (hX'.mono Set.inter_subset_left)
      (hY.mono Set.inter_subset_right) (hY.mono Set.inter_subset_right)
      (hZ.mono Set.inter_subset_right) (hZ.mono Set.inter_subset_right)
      (fun y hy ↦ hXX' y hy.1) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hxS
  · intro V hV hxV f X hf hX
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    exact D.curvatureOnFields_smul_left hS f X Y Z
      (hf.mono Set.inter_subset_left) (hX.mono Set.inter_subset_left)
      (hY.mono Set.inter_subset_right) (hZ.mono Set.inter_subset_right)
      ⟨hxV, hx⟩
  · intro V hV hxV X X' hX hX'
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    exact D.curvatureOnFields_add_left hS X X' Y Z
      (hX.mono Set.inter_subset_left) (hX'.mono Set.inter_subset_left)
      (hY.mono Set.inter_subset_right) (hZ.mono Set.inter_subset_right)
      ⟨hxV, hx⟩

private theorem tensorial_second (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    {x : M} (hx : x ∈ U) {X Z : Vec n M}
    (hX : VecSmooth U X) (hZ : VecSmooth U Z) :
    SmoothTensorialOn (I := 𝓡 n) (F := EuclideanSpace ℝ (Fin n))
      (fun Y ↦ D.curvatureOnFields X Y Z x) x := by
  refine ⟨?_, ?_, ?_⟩
  · intro V hV hxV Y Y' hY hY' hYY'
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    have hxS : x ∈ S := ⟨hxV, hx⟩
    exact D.curvatureOnFields_congr_of_eqOn hS X X Y Y' Z Z
      (hX.mono Set.inter_subset_right) (hX.mono Set.inter_subset_right)
      (hY.mono Set.inter_subset_left) (hY'.mono Set.inter_subset_left)
      (hZ.mono Set.inter_subset_right) (hZ.mono Set.inter_subset_right)
      (fun _ _ ↦ rfl) (fun y hy ↦ hYY' y hy.1) (fun _ _ ↦ rfl) hxS
  · intro V hV hxV f Y hf hY
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    exact D.curvatureOnFields_smul_second hS f X Y Z
      (hf.mono Set.inter_subset_left) (hX.mono Set.inter_subset_right)
      (hY.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_right)
      ⟨hxV, hx⟩
  · intro V hV hxV Y Y' hY hY'
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    exact D.curvatureOnFields_add_second hS X Y Y' Z
      (hX.mono Set.inter_subset_right) (hY.mono Set.inter_subset_left)
      (hY'.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_right)
      ⟨hxV, hx⟩

private theorem tensorial_third (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    {x : M} (hx : x ∈ U) {X Y : Vec n M}
    (hX : VecSmooth U X) (hY : VecSmooth U Y) :
    SmoothTensorialOn (I := 𝓡 n) (F := EuclideanSpace ℝ (Fin n))
      (fun Z ↦ D.curvatureOnFields X Y Z x) x := by
  refine ⟨?_, ?_, ?_⟩
  · intro V hV hxV Z Z' hZ hZ' hZZ'
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    have hxS : x ∈ S := ⟨hxV, hx⟩
    exact D.curvatureOnFields_congr_of_eqOn hS X X Y Y Z Z'
      (hX.mono Set.inter_subset_right) (hX.mono Set.inter_subset_right)
      (hY.mono Set.inter_subset_right) (hY.mono Set.inter_subset_right)
      (hZ.mono Set.inter_subset_left) (hZ'.mono Set.inter_subset_left)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun y hy ↦ hZZ' y hy.1) hxS
  · intro V hV hxV f Z hf hZ
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    exact D.curvatureOnFields_smul_third hS f X Y Z
      (hf.mono Set.inter_subset_left) (hX.mono Set.inter_subset_right)
      (hY.mono Set.inter_subset_right) (hZ.mono Set.inter_subset_left)
      ⟨hxV, hx⟩
  · intro V hV hxV Z Z' hZ hZ'
    let S := V ∩ U
    have hS : IsOpen S := hV.inter hU
    exact D.curvatureOnFields_add_third hS X Y Z Z'
      (hX.mono Set.inter_subset_right) (hY.mono Set.inter_subset_right)
      (hZ.mono Set.inter_subset_left) (hZ'.mono Set.inter_subset_left)
      ⟨hxV, hx⟩

theorem curvatureOnFields_left_eq_of_eq_at
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (X X' Y Z : Vec n M) (hX : VecSmooth U X) (hX' : VecSmooth U X')
    (hY : VecSmooth U Y) (hZ : VecSmooth U Z) (hXX' : X x = X' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y Z x :=
  SmoothTensorialOn.pointwise (tensorial_left D hU hx hY hZ) hU hx hX hX' hXX'

theorem curvatureOnFields_second_eq_of_eq_at
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (X Y Y' Z : Vec n M) (hX : VecSmooth U X) (hY : VecSmooth U Y) (hY' : VecSmooth U Y')
    (hZ : VecSmooth U Z) (hYY' : Y x = Y' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X Y' Z x :=
  SmoothTensorialOn.pointwise (tensorial_second D hU hx hX hZ) hU hx hY hY' hYY'

theorem curvatureOnFields_third_eq_of_eq_at
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (X Y Z Z' : Vec n M) (hX : VecSmooth U X) (hY : VecSmooth U Y)
    (hZ : VecSmooth U Z) (hZ' : VecSmooth U Z') (hZZ' : Z x = Z' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X Y Z' x :=
  SmoothTensorialOn.pointwise (tensorial_third D hU hx hX hY) hU hx hZ hZ' hZZ'


theorem curvatureOnFields_eq_of_eq_at
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (X X' Y Y' Z Z' : Vec n M)
    (hX : VecSmooth U X) (hX' : VecSmooth U X')
    (hY : VecSmooth U Y) (hY' : VecSmooth U Y')
    (hZ : VecSmooth U Z) (hZ' : VecSmooth U Z')
    (hXX' : X x = X' x) (hYY' : Y x = Y' x) (hZZ' : Z x = Z' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y' Z' x := by
  calc
    _ = D.curvatureOnFields X' Y Z x :=
      D.curvatureOnFields_left_eq_of_eq_at hU hx X X' Y Z hX hX' hY hZ hXX'
    _ = D.curvatureOnFields X' Y' Z x :=
      D.curvatureOnFields_second_eq_of_eq_at hU hx X' Y Y' Z hX' hY hY' hZ hYY'
    _ = D.curvatureOnFields X' Y' Z' x :=
      D.curvatureOnFields_third_eq_of_eq_at hU hx X' Y' Z Z' hX' hY' hZ hZ' hZZ'





theorem contMDiffOn_extend_baseSet (x : M) (v : TangentSpace (𝓡 n) x) :
    VecSmooth (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x).baseSet
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  suffices ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun y ↦ (e ⟨y, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y⟩).2)
      e.baseSet by
    intro y hy
    rw [e.contMDiffWithinAt_section _ hy]
    exact this y hy
  let w := (e ⟨x, v⟩).2
  have hw : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun _ : M ↦ w) e.baseSet := contMDiffOn_const
  exact hw.congr (fun y hy ↦ by
    simpa [FiberBundle.extend, e, w] using
      (e.continuousLinearEquivAt ℝ y hy).apply_symm_apply ((e ⟨x, v⟩).2))


theorem curvatureOnFields_eq_curvature
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z : Vec n M) (hX : VecSmooth U X) (hY : VecSmooth U Y) (hZ : VecSmooth U Z)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x = D.curvature x (X x) (Y x) (Z x) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let S := U ∩ e.baseSet
  have hS : IsOpen S := hU.inter e.open_baseSet
  have hxS : x ∈ S := ⟨hx, FiberBundle.mem_baseSet_trivializationAt _ _ x⟩
  exact D.curvatureOnFields_eq_of_eq_at hS hxS X
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (X x)) Y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x)) Z
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Z x))
    (hX.mono Set.inter_subset_left)
    ((contMDiffOn_extend_baseSet x (X x)).mono Set.inter_subset_right)
    (hY.mono Set.inter_subset_left)
    ((contMDiffOn_extend_baseSet x (Y x)).mono Set.inter_subset_right)
    (hZ.mono Set.inter_subset_left)
    ((contMDiffOn_extend_baseSet x (Z x)).mono Set.inter_subset_right)
    (by simp) (by simp) (by simp)


theorem curvatureTensor_multilinear (D : LeviCivitaData g) (x : M) :
    ∃ A : MultilinearMap ℝ (fun _ : Fin 4 ↦ TangentSpace (𝓡 n) x) ℝ,
      ∀ v, D.riemannEvaluation x v = A v := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let U := e.baseSet
  have hU : IsOpen U := e.open_baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt _ _ x
  let ext (v : TangentSpace (𝓡 n) x) : Vec n M :=
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hext (v : TangentSpace (𝓡 n) x) : VecSmooth U (ext v) := by
    exact contMDiffOn_extend_baseSet x v
  let F : (Fin 4 → TangentSpace (𝓡 n) x) → ℝ := fun v ↦
    D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)
  let A : MultilinearMap ℝ (fun _ : Fin 4 ↦ TangentSpace (𝓡 n) x) ℝ :=
    MultilinearMap.mk' F (by
      intro m i a b
      fin_cases i
      · have h := D.curvatureOnFields_left_eq_of_eq_at hU hx
          (ext (a + b)) (ext a + ext b) (ext (m 1)) (ext (m 3))
          (hext _) ((hext a).add_section (hext b)) (hext _) (hext _)
          (by simp [ext])
        simp only [Fin.isValue, Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero,
          not_false_eq_true, Function.update_of_ne, Fin.reduceEq, F]
        unfold curvatureTensor curvature
        rw [h, D.curvatureOnFields_add_left hU (ext a) (ext b)
          (ext (m 1)) (ext (m 3)) (hext _) (hext _) (hext _) (hext _) hx]
        simp [ext, add_apply, map_add]
      · have h := D.curvatureOnFields_second_eq_of_eq_at hU hx
          (ext (m 0)) (ext (a + b)) (ext a + ext b) (ext (m 3))
          (hext _) (hext _) ((hext a).add_section (hext b)) (hext _)
          (by simp [ext])
        simp only [Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
          Function.update_of_ne, Function.update_self, Fin.reduceEq, F]
        unfold curvatureTensor curvature
        rw [h, D.curvatureOnFields_add_second hU (ext (m 0)) (ext a) (ext b)
          (ext (m 3)) (hext _) (hext _) (hext _) (hext _) hx]
        simp [ext, add_apply, map_add]
      · simp only [Fin.isValue, Fin.reduceFinMk, ne_eq, Fin.reduceEq, not_false_eq_true,
          Function.update_of_ne, Function.update_self, F]
        unfold curvatureTensor curvature
        simp only [map_add]
      · have h := D.curvatureOnFields_third_eq_of_eq_at hU hx
          (ext (m 0)) (ext (m 1)) (ext (a + b)) (ext a + ext b)
          (hext _) (hext _) (hext _) ((hext a).add_section (hext b))
          (by simp [ext])
        simp only [Fin.isValue, Fin.reduceFinMk, ne_eq, Fin.reduceEq, not_false_eq_true,
          Function.update_of_ne, Function.update_self, F]
        unfold curvatureTensor curvature
        rw [h, D.curvatureOnFields_add_third hU (ext (m 0)) (ext (m 1))
          (ext a) (ext b) (hext _) (hext _) (hext _) (hext _) hx]
        simp [ext, add_apply, map_add])
      (by
        intro m i c a
        fin_cases i
        · have h := D.curvatureOnFields_left_eq_of_eq_at hU hx
            (ext (c • a)) ((fun _ : M ↦ c) • ext a) (ext (m 1)) (ext (m 3))
            (hext _) (contMDiffOn_const.smul_section (hext a)) (hext _) (hext _)
            (by simp [ext])
          simp only [Fin.isValue, Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero,
            not_false_eq_true, Function.update_of_ne, Fin.reduceEq, smul_eq_mul, F]
          unfold curvatureTensor curvature
          rw [h, D.curvatureOnFields_smul_left hU (fun _ : M ↦ c) (ext a)
            (ext (m 1)) (ext (m 3)) contMDiffOn_const (hext _) (hext _) (hext _) hx]
          simp [ext, map_smul]
        · have h := D.curvatureOnFields_second_eq_of_eq_at hU hx
            (ext (m 0)) (ext (c • a)) ((fun _ : M ↦ c) • ext a) (ext (m 3))
            (hext _) (hext _) (contMDiffOn_const.smul_section (hext a)) (hext _)
            (by simp [ext])
          simp only [Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, Function.update_self, Fin.reduceEq, smul_eq_mul, F]
          unfold curvatureTensor curvature
          rw [h, D.curvatureOnFields_smul_second hU (fun _ : M ↦ c) (ext (m 0))
            (ext a) (ext (m 3)) contMDiffOn_const (hext _) (hext _) (hext _) hx]
          simp [ext, map_smul]
        · simp only [Fin.isValue, Fin.reduceFinMk, ne_eq, Fin.reduceEq, not_false_eq_true,
            Function.update_of_ne, Function.update_self, smul_eq_mul, F]
          unfold curvatureTensor curvature
          simp [smul_eq_mul]
        · have h := D.curvatureOnFields_third_eq_of_eq_at hU hx
            (ext (m 0)) (ext (m 1)) (ext (c • a)) ((fun _ : M ↦ c) • ext a)
            (hext _) (hext _) (hext (c • a))
            (contMDiffOn_const.smul_section (hext a))
            (by simp [ext])
          simp only [Fin.isValue, Fin.reduceFinMk, ne_eq, Fin.reduceEq, not_false_eq_true,
            Function.update_of_ne, Function.update_self, smul_eq_mul, F]
          unfold curvatureTensor curvature
          rw [h, D.curvatureOnFields_smul_third hU (fun _ : M ↦ c) (ext (m 0))
            (ext (m 1)) (ext a) contMDiffOn_const (hext _) (hext _) (hext _) hx]
          simp [ext, map_smul])
  refine ⟨A, ?_⟩
  intro v
  rfl


theorem riemannEvaluation_smooth (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X : Fin 4 → Vec n M)
    (hX : ∀ i, VecSmooth U (X i)) :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ D.riemannEvaluation x (fun i ↦ X i x)) U := by
  have h := D.curvatureOnFields_smooth hU (X 0) (X 1) (X 3) (X 2)
    (hX 0) (hX 1) (hX 3) (hX 2)
  apply h.congr
  intro x hx
  rw [D.curvatureOnFields_eq_curvature hU (X 0) (X 1) (X 3)
    (hX 0) (hX 1) (hX 3) hx]
  rfl

end LeviCivitaData

end PoincareConjecture
