import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

lemma inner_normalize_eq_one (g : RiemannianMetric 2 S) (x : S)
    (v : TangentSpace (𝓡 2) x) (hv : 0 < g.inner x v v) :
    g.inner x ((Real.sqrt (g.inner x v v))⁻¹ • v)
      ((Real.sqrt (g.inner x v v))⁻¹ • v) = 1 := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp
  exact (Real.sq_sqrt hv.le).symm

lemma contMDiffOn_normalize (g : RiemannianMetric 2 S)
    {U : Set S} {V : (x : S) → TangentSpace (𝓡 2) x}
    (hV : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) U)
    (hpos : ∀ x ∈ U, 0 < g.inner x (V x) (V x)) :
    ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (T% (fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  intro x hx
  have hs := (Real.contDiffAt_sqrt (hpos x hx).ne').comp_contMDiffWithinAt
    (f := fun y => g.inner y (V y) (V y))
    ((hV x hx).inner_bundle (hV x hx))
  exact (hs.inv₀ (Real.sqrt_ne_zero'.mpr (hpos x hx))).smul_section (hV x hx)

theorem exists_local_orthonormal_frame (g : RiemannianMetric 2 S) (p : S) :
    ∃ (U : Set S) (e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x),
      IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) p) = 2 :=
    finrank_euclideanSpace_fin
  let b := (g.orthonormalBasis p).reindex (finCongr hdim)
  have hb (i j : Fin 2) : g.inner p (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  obtain ⟨U₀, hU₀, hp₀, hframe⟩ := exists_open_contMDiffOn_extend (n := 2) p
  let A := FiberBundle.extend (EuclideanSpace ℝ (Fin 2)) (b 0)
  let B := FiberBundle.extend (EuclideanSpace ℝ (Fin 2)) (b 1)
  have hA : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% A) U₀ := hframe (b 0)
  have hB : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% B) U₀ := hframe (b 1)
  let q₁ : S → ℝ := fun x => g.inner x (A x) (A x)
  have hq₁ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ q₁ U₀ := hA.inner_bundle hA
  have hq₁p : q₁ p = 1 := by simp [q₁, A, hb]
  let U₁ := U₀ ∩ q₁ ⁻¹' Ioi 0
  have hU₁ : IsOpen U₁ := hq₁.continuousOn.isOpen_inter_preimage hU₀ isOpen_Ioi
  have hp₁ : p ∈ U₁ := ⟨hp₀, by simp [hq₁p]⟩
  let e₁ := fun x => (Real.sqrt (q₁ x))⁻¹ • A x
  have he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U₁ :=
    g.contMDiffOn_normalize (hA.mono inter_subset_left) (fun _ hx => hx.2)
  have he₁unit (x : S) (hx : x ∈ U₁) : g.inner x (e₁ x) (e₁ x) = 1 :=
    g.inner_normalize_eq_one x (A x) hx.2
  have he₁p : e₁ p = b 0 := by simp [e₁, hq₁p, A]
  let C := fun x => B x - g.inner x (e₁ x) (B x) • e₁ x
  have hC : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% C) U₁ :=
    (hB.mono inter_subset_left).sub_section
      ((he₁.inner_bundle (hB.mono inter_subset_left)).smul_section he₁)
  have hCp : C p = b 1 := by simp [C, he₁p, B, hb]
  have horthC (x : S) (hx : x ∈ U₁) : g.inner x (e₁ x) (C x) = 0 := by
    simp only [C, map_sub, map_smul, smul_eq_mul, he₁unit x hx, mul_one, sub_self]
  let q₂ : S → ℝ := fun x => g.inner x (C x) (C x)
  have hq₂ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ q₂ U₁ := hC.inner_bundle hC
  have hq₂p : q₂ p = 1 := by simp [q₂, hCp, hb]
  let U₂ := U₁ ∩ q₂ ⁻¹' Ioi 0
  have hU₂ : IsOpen U₂ := hq₂.continuousOn.isOpen_inter_preimage hU₁ isOpen_Ioi
  have hp₂ : p ∈ U₂ := ⟨hp₁, by simp [hq₂p]⟩
  let e₂ := fun x => (Real.sqrt (q₂ x))⁻¹ • C x
  have he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U₂ :=
    g.contMDiffOn_normalize (hC.mono inter_subset_left) (fun _ hx => hx.2)
  refine ⟨U₂, e₁, e₂, hU₂, hp₂, he₁.mono inter_subset_left, he₂,
    fun x hx => he₁unit x hx.1, fun x hx => ?_, fun x hx => ?_⟩
  · exact g.inner_normalize_eq_one x (C x) hx.2
  · simp only [e₂, map_smul, smul_eq_mul, horthC x hx.1, mul_zero]

theorem exists_aligned_orthonormal_frame_of_independent_fields (g : RiemannianMetric 2 S)
    {U : Set S} {X Y : (x : S) → TangentSpace (𝓡 2) x}
    (hX : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Y) U)
    (hlin : ∀ x ∈ U, LinearIndependent ℝ ![X x, Y x]) :
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0) ∧
      (∀ x ∈ U, 0 <
        g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) ∧
      e₁ = fun x => (Real.sqrt (g.inner x (X x) (X x)))⁻¹ • X x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  have hXne (x : S) (hx : x ∈ U) : X x ≠ 0 := by
    simpa using (hlin x hx).ne_zero 0
  have hq₁ (x : S) (hx : x ∈ U) : 0 < g.inner x (X x) (X x) :=
    real_inner_self_pos.mpr (hXne x hx)
  let e₁ := fun x => (Real.sqrt (g.inner x (X x) (X x)))⁻¹ • X x
  have he₁ := g.contMDiffOn_normalize hX hq₁
  have hu₁ (x : S) (hx : x ∈ U) : g.inner x (e₁ x) (e₁ x) = 1 :=
    g.inner_normalize_eq_one x (X x) (hq₁ x hx)
  let C := fun x => Y x - g.inner x (e₁ x) (Y x) • e₁ x
  have hC : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% C) U :=
    hY.sub_section ((he₁.inner_bundle hY).smul_section he₁)
  have hCne (x : S) (hx : x ∈ U) : C x ≠ 0 := by
    intro hz
    have heq : Y x =
        (g.inner x (e₁ x) (Y x) * (Real.sqrt (g.inner x (X x) (X x)))⁻¹) • X x := by
      simpa only [C, sub_eq_zero, e₁, smul_smul] using hz
    exact (LinearIndependent.pair_iff' (hXne x hx)).mp (hlin x hx) _ heq.symm
  have hq₂ (x : S) (hx : x ∈ U) : 0 < g.inner x (C x) (C x) :=
    real_inner_self_pos.mpr (hCne x hx)
  let e₂ := fun x => (Real.sqrt (g.inner x (C x) (C x)))⁻¹ • C x
  have he₂ := g.contMDiffOn_normalize hC hq₂
  have hu₂ (x : S) (hx : x ∈ U) : g.inner x (e₂ x) (e₂ x) = 1 :=
    g.inner_normalize_eq_one x (C x) (hq₂ x hx)
  have horth (x : S) (hx : x ∈ U) : g.inner x (e₁ x) (e₂ x) = 0 := by
    simp only [e₂, C, map_smul, map_sub, smul_eq_mul, hu₁ x hx, mul_one, sub_self,
      mul_zero]
  refine ⟨e₁, e₂, he₁, he₂, hu₁, hu₂, horth, ?_, rfl⟩
  intro x hx
  have hs₁ := Real.sqrt_pos.mpr (hq₁ x hx)
  have hs₂ := Real.sqrt_pos.mpr (hq₂ x hx)
  have hXe : X x = Real.sqrt (g.inner x (X x) (X x)) • e₁ x := by
    simp [e₁, smul_smul, hs₁.ne']
  have hCe : C x = Real.sqrt (g.inner x (C x) (C x)) • e₂ x := by
    simp [e₂, smul_smul, hs₂.ne']
  have hX₁ : g.inner x (X x) (e₁ x) = Real.sqrt (g.inner x (X x) (X x)) := by
    conv_lhs => rw [hXe]
    simp only [map_smul, smul_apply, smul_eq_mul, hu₁ x hx, mul_one]
  have hX₂ : g.inner x (X x) (e₂ x) = 0 := by
    rw [hXe]
    simp only [map_smul, smul_apply, smul_eq_mul, horth x hx, mul_zero]
  have hY₂ : g.inner x (Y x) (e₂ x) = Real.sqrt (g.inner x (C x) (C x)) := by
    have hc := congrArg (fun v => g.inner x v (e₂ x)) hCe
    simpa only [C, map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
      horth x hx, hu₂ x hx, mul_zero, sub_zero, mul_one] using hc
  rw [hX₁, hX₂, hY₂, zero_mul, sub_zero]
  exact mul_pos hs₁ hs₂

theorem exists_orthonormal_frame_of_independent_fields (g : RiemannianMetric 2 S)
    {U : Set S} {X Y : (x : S) → TangentSpace (𝓡 2) x}
    (hX : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Y) U)
    (hlin : ∀ x ∈ U, LinearIndependent ℝ ![X x, Y x]) :
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0) ∧
      ∀ x ∈ U, 0 <
        g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x) := by
  obtain ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp, _⟩ :=
    g.exists_aligned_orthonormal_frame_of_independent_fields hX hY hlin
  exact ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp⟩

end PoincareConjecture.RiemannianMetric
